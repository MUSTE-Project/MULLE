{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
{-# Language
 DeriveGeneric,
 DerivingStrategies,
 FlexibleContexts,
 GeneralizedNewtypeDeriving,
 MultiParamTypeClasses,
 OverloadedStrings,
 ScopedTypeVariables,
 StandaloneDeriving,
 TypeApplications,
 TypeFamilies,
 UndecidableInstances
#-}

{- | This Module is the internal implementation behind the module 'Muste.Grammar' -}
module Muste.Grammar
  ( Grammar(..)
  , Rule(..)
  -- Used internally
  , isEmptyGrammar
  , getAllRules
  , getRuleType
  , brackets
  , parseTTree
  , MonadGrammar(..)
  , GrammarT
  , runGrammarT
  , getGrammar
  , getGrammarOneOff
  , parseSentence
  , getMetas
  , getFunctions
  , getFunNames
  , hole
  , HasKnownGrammars(..)
  , KnownGrammars
  , noGrammars
  , bracketsToTuples
  ) where

import Control.Applicative (Alternative)
import Control.Category ((>>>))
import Control.Monad (MonadPlus)
import Control.Monad.Base (MonadBase)
import Control.Monad.Except (ExceptT)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.Reader (MonadReader, ReaderT)
import qualified Control.Monad.Reader as Reader
import Control.Monad.Trans (MonadTrans(lift))
import Control.Monad.Trans.Control (MonadBaseControl)
import Data.IORef (IORef)
import qualified Data.IORef as IO
import GHC.Generics (Generic)
import Snap (MonadSnap)
import qualified Snap

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (union, partition)
import Data.Text (Text)
import qualified Data.Text as Text
import Text.Printf (printf)
import Data.Text.Prettyprint.Doc (Pretty(..))
import qualified Data.Text.Prettyprint.Doc as Doc
import Data.String.Conversions (convertString)
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet

-- This might be the only place we should know of PGF
import qualified PGF
import qualified PGF.Internal as PGFI

import Muste.Util (wildCard)
import qualified Muste.Tree as Tree
import Muste.Tree (TTree(TNode,TMeta), Category, Path, FunType(Fun,NoType))


-- | Type 'Rule' consists of a 'String' representing the function name
-- and a 'FunType' representing its type.
data Rule = Function Category FunType deriving (Ord,Eq,Show,Read)

deriving instance Generic Rule

-- | Type 'Grammar' consists of a start category and a list of rules.
data Grammar = Grammar
  { startcat :: Category
  , synrules :: [Rule]
  , lexrules :: [Rule]
  , pgf :: PGF.PGF
  }

instance Pretty Grammar where
  pretty (Grammar sCat srules lrules _) = Doc.sep
    [ p "Startcat: %s" (show sCat)
    , p "Syntactic Rules: %s" (s srules)
    , p "Lexical Rules: %s" (s lrules)
    ]
    where
    s = unwords . map (\r -> "\t" ++ show r ++ "\n")
    p :: String -> String -> Doc.Doc ann
    p frmt s = Doc.pretty @String $ printf frmt s

-- | The function 'getRules' returns the union of syntactic and
-- lexical rules of a grammar.
getAllRules :: Grammar -> [Rule]
getAllRules g = synrules g `union` lexrules g

-- | The function 'getRuleType' extracts the full type of a rule
getRuleType :: Rule -> FunType
getRuleType (Function _ funType) = funType

-- | Constant for an empty 'Grammar' in line with 'emptyPGF'
emptyGrammar :: Grammar
emptyGrammar = Grammar wildCard [] [] PGFI.emptyPGF

-- | Predicate to check if a PGF is empty, i.e. when the absname is
-- PGF.wildCId
isEmptyPGF :: PGF.PGF -> Bool
isEmptyPGF pgf = PGFI.absname pgf == PGF.wildCId

-- | Predicate to check if a Grammar is empty, i.e. when the startcat
-- is PGF.wildCId and pgf is empty
isEmptyGrammar :: Grammar -> Bool
isEmptyGrammar grammar = startcat grammar == wildCard && isEmptyPGF (pgf grammar)

-- | The function 'getFunTypeWithGrammar' extracts the function type from a Grammar given a function name
getFunType :: Grammar -> Category -> FunType
getFunType g id =
  let
    rules = filter (\r -> getRuleName r == id) $ getAllRules g
  in
    if not $ null rules then getRuleType $ head rules else NoType

-- | The function 'getRuleName' extracts the name of a rule
getRuleName :: Rule -> Category
getRuleName (Function name _) = name

-- | The function 'pgfToGrammar' transforms a PGF grammar to a simpler grammar data structure
pgfToGrammar :: PGF.PGF -> Grammar
pgfToGrammar pgf
  | isEmptyPGF pgf = emptyGrammar
  | otherwise =
    let
      -- Get function names
      funs = PGF.functions pgf
      -- Get their types
      funtypes = map (getFunTypeWithPGF pgf) funs
      -- Combine to a rule
      rules = zipWith Function (map cIdToCat funs) funtypes
      -- Split in lexical and syntactical rules
      (lexrules,synrules) = partition (\r -> case r of { Function _ (Fun _ []) -> True ; _ -> False } ) rules
      -- Get the startcat from the PGF
      (_, startcat, _) = PGFI.unType (PGF.startCat pgf)
    in
      Grammar (cIdToCat startcat) synrules lexrules pgf
  where
    getFunTypeWithPGF :: PGF.PGF -> PGF.CId -> FunType
    getFunTypeWithPGF grammar id
      | isEmptyPGF grammar = NoType -- Empty grammar
      | otherwise =
        let
          typ = PGF.functionType grammar id
        in
          case typ of {
            Nothing -> NoType ; -- No type found in grammar
            Just t ->
            let
              (hypos,typeid,_exprs) = PGFI.unType t
              cats = map (\(_,_,PGFI.DTyp _ cat _) -> cat) hypos
            in
              Fun (cIdToCat typeid) (map cIdToCat cats)
            }


brackets :: Grammar -> PGF.Language -> TTree -> [PGF.BracketedString]
brackets grammar language ttree
  = PGF.bracketedLinearize (pgf grammar) language (toGfTree ttree)


-- | Convert a 'PGF.BracketedString' to a list of string/path tuples.
bracketsToTuples :: TTree -> PGF.BracketedString -> [(Text, Path)]
bracketsToTuples = deep
  where
  deep :: TTree -> PGF.BracketedString -> [(Text, Path)]
  deep _     (PGF.Bracket _ _   _ _ _ _ []) = mempty
  -- Ordinary leaf
  deep ltree (PGF.Bracket _ fid _ _ _ _ [PGF.Leaf token]) =
    [(Text.pack token, Tree.getPath ltree fid)]
  -- Meta leaf
  deep ltree (PGF.Bracket _ fid _ _ _ [PGFI.EMeta i] _) =
    [("?" <> Text.pack (show i), Tree.getPath ltree fid)]
  -- In the middle of the tree
  deep ltree (PGF.Bracket _ fid _ _ _ _ bs) =
    broad ltree fid bs mempty
  deep _ _ = error "Muste.bracketsToTuples: Non-exhaustive pattern match"
  broad :: TTree -> Int -> [PGF.BracketedString] -> [(Text, Path)] -> [(Text, Path)]
  -- End of node siblings
  broad _     _   []                 ts = ts
  -- Syncategorial word
  broad ltree fid (PGF.Leaf token:bss) ts = (x:xs)
    where
    x = (Text.pack token, Tree.getPath ltree fid)
    xs = broad ltree fid bss ts
  -- In the middle of the nodes
  broad ltree fid (bs:bss)
    ts = deep ltree bs ++ broad ltree fid bss ts


parseTTree :: Grammar -> String -> TTree
parseTTree g = fromGfTree g . read

-- | Creates a GF abstract syntax Tree from a generic tree.
toGfTree :: TTree -> PGF.Tree
toGfTree tree =
  let
    loop :: [TTree] -> Int -> (Int,[PGF.Tree])
    loop [] id = (id,[])
    loop (t:ts) id =
      let
        (nid,nt) = convert t id
        (fid,nts) = loop ts nid
      in
        (fid,nt:nts)
    convert :: TTree -> Int -> (Int,PGF.Tree)
    convert (TMeta _) id = (id + 1, PGF.mkMeta id)
    convert (TNode name _ ns) id =
      let
        (nid,nts) = loop ns id
      in
        if name == wildCard then (nid,PGF.mkApp PGF.wildCId nts) else (nid,PGF.mkApp (catToCid name) nts)
  in
    snd $ convert tree 0

catToCid :: Category -> PGF.CId
catToCid = Tree.unCategory >>> convertString >>> PGF.utf8CId

-- FIXME A 'PGF.CId' is just a newtype wrapper around a 'ByteString'.
-- If we could just get at that somehow.  If [this PR][PR#9] goes
-- through we will be able to do this.
--
-- [PR#9]: https://github.com/GrammaticalFramework/gf-core/pull/9
cIdToCat :: PGF.CId -> Category
cIdToCat = PGF.showCId >>> Text.pack >>> Tree.Category

-- | The function 'fromGfTree' creates a 'TTree' from a 'PGF.Tree' and
-- a 'Grammar'. Handles only 'EApp' and 'EFun'. Generates a 'hole' in
-- unsupported cases.
fromGfTree :: Grammar -> PGF.Tree -> TTree
fromGfTree g (PGFI.EFun f) =
  let
    typ = getFunType g (cIdToCat f)
  in
    TNode (cIdToCat f) typ []
fromGfTree g (PGFI.EApp e1 e2) =
  let
    (TNode name typ sts) = fromGfTree g e1
    st2 = fromGfTree g e2
  in
    TNode name typ (sts ++ [st2])
fromGfTree _ _ = hole

hole :: TTree
hole = TMeta wildCard

newtype KnownGrammars = KnownGrammars
  -- No pun.
  { unKnownGrammars :: IORef (Map Text Grammar)
  }

noGrammars :: MonadIO io => io KnownGrammars
noGrammars = KnownGrammars <$> liftIO (IO.newIORef mempty)

-- | A monad for managing loaded grammars.
newtype GrammarT m a = GrammarT ( ReaderT KnownGrammars m a )

deriving newtype instance Functor m => Functor (GrammarT m)
deriving newtype instance Monad m => Applicative (GrammarT m)
deriving newtype instance Monad m => Monad (GrammarT m)
deriving newtype instance Monad m => MonadReader KnownGrammars (GrammarT m)
deriving newtype instance MonadIO m => MonadIO (GrammarT m)
deriving newtype instance MonadTrans GrammarT
deriving newtype instance MonadBaseControl IO m => MonadBaseControl IO (GrammarT m)
deriving newtype instance MonadBase IO m => MonadBase IO (GrammarT m)
deriving newtype instance (Alternative m, Monad m) => Alternative (GrammarT m)
deriving newtype instance (MonadSnap m) => MonadSnap (GrammarT m)
deriving newtype instance MonadPlus m => MonadPlus (GrammarT m)

class MonadIO m => MonadGrammar m where
  -- | Get the known grammars
  getKnownGrammars :: m (Map Text Grammar)
  -- | Update the known grammars with.
  insertGrammar :: Text -> Grammar -> m ()

instance MonadIO io => MonadGrammar (GrammarT io) where
  getKnownGrammars
    =   Reader.ask
    >>= liftIO . IO.readIORef . unKnownGrammars
  insertGrammar t g = do
    KnownGrammars ref  <- Reader.ask
    liftIO $ IO.modifyIORef ref $ Map.insert t g

-- Even though 'GrammarT' is implemented with a reader monad notice
-- that we pass through it here...
instance MonadGrammar m => MonadGrammar (ReaderT r m) where
  getKnownGrammars = lift getKnownGrammars
  insertGrammar t g = lift $ insertGrammar t g

instance MonadGrammar m => MonadGrammar (ExceptT r m) where
  getKnownGrammars = lift getKnownGrammars
  insertGrammar t g = lift $ insertGrammar t g

class HasKnownGrammars g where
  giveKnownGrammars :: g -> KnownGrammars

instance HasKnownGrammars w => MonadGrammar (Snap.Handler v w) where
  -- Implementation is almost identitcal to that of 'GrammarT'...
  getKnownGrammars = do
    ref <- unKnownGrammars . giveKnownGrammars <$> Reader.ask @_ @(Snap.Handler _ _)
    mp <- liftIO $ IO.readIORef ref
    liftIO $ do
      putStrLn "getKnownGrammars @Snap.Handler"
      print $ Map.size mp
    pure mp
  insertGrammar t g = do
    KnownGrammars ref  <- giveKnownGrammars <$> Reader.ask
    liftIO $ IO.modifyIORef ref $ Map.insert t g

runGrammarT :: MonadIO io => GrammarT io a -> io a
runGrammarT (GrammarT m) = do
  r <- liftIO $ IO.newIORef mempty
  Reader.runReaderT m (KnownGrammars r)

readGrammar :: MonadIO io => Text -> io Grammar
readGrammar p = liftIO $ do g <- PGF.readPGF $ Text.unpack p
                            return $ pgfToGrammar g

-- | Looks for a grammar at the specified location.  If the grammar is
-- found it is added to the known grammars and returned.  If the
-- grammar is not found a 'FileNotFoundException' is thrown.
getGrammar :: forall m . MonadGrammar m => Text -> m Grammar
getGrammar idf = do
  m <- getKnownGrammars
  case Map.lookup idf m of
    Nothing -> loadAndInsert idf
    Just a -> pure a

-- | A convenience method wrapping 'getGrammar' that just gets the
-- grammar once but without all the nice memoization offered by
-- 'MonadGrammar'.
getGrammarOneOff :: MonadIO io => Text -> io Grammar
getGrammarOneOff = runGrammarT . getGrammar

loadAndInsert :: forall m . MonadGrammar m => Text -> m Grammar
loadAndInsert idf = do
  g <- readGrammar idf
  insertGrammar idf g
  pure g

-- | Parses a linearized sentence.  Essentially a wrapper around
-- 'PGF.parse'.
parseSentence :: Grammar -> PGF.Language -> Text -> [TTree]
parseSentence grammar lang = Text.unpack >>> pgfIfy >>> fmap musteIfy
  where
  pgfIfy :: String -> [PGF.Tree]
  pgfIfy = PGF.parse p lang (PGF.startCat p)
  musteIfy :: PGF.Tree -> TTree
  musteIfy = fromGfTree grammar
  p :: PGF.PGF
  p = pgf grammar

-- | Returns a bag of all meta-variables in a tree.
getMetas :: TTree -> MultiSet Category
getMetas (TMeta cat)    = MultiSet.singleton cat
getMetas (TNode _ _ ts) = mconcat $ getMetas <$> ts

-- | Returns a bag of all functions in a tree.
getFunctions :: TTree -> MultiSet Rule
getFunctions = Tree.foldMapTTree step
  where
  step fun typ = MultiSet.singleton $ Function fun typ

-- | Returns a set of all function names in a tree.
getFunNames :: TTree -> Set Category
getFunNames = Tree.foldMapTTree step
    where step fun _ = Set.singleton fun
