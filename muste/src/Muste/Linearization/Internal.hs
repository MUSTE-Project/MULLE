{-# OPTIONS_GHC -Wno-unused-top-binds -Wno-name-shadowing #-}
{-# Language CPP, OverloadedStrings #-}
module Muste.Linearization.Internal
  ( Context(..)
  , buildContext
  , Linearization
  , LinToken
  , ltpath
  , linearizeTree
  , langAndContext
  , mkLin
  , sameOrder
  , disambiguate
  -- Used in test suite:
  , readLangs
  , stringRep
  ) where

import Data.Maybe (fromMaybe)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Aeson
import GHC.Generics (Generic)
import Data.Binary (Binary)
-- This might be the only place we should know of PGF
import qualified PGF
import qualified PGF.Internal as PGF hiding (funs, cats)
import Data.Function (on)
import Text.Printf
#if MIN_VERSION_base(4,11,0)
#else
import Data.Semigroup (Semigroup((<>)))
#endif
import Data.MonoTraversable
  ( Element, MonoTraversable(..), MonoFunctor
  , MonoFoldable(..), GrowingAppend, MonoPointed
  )
import qualified Data.MonoTraversable as Mono
import Data.Sequences (SemiSequence, IsSequence, Index)
import qualified Data.Sequences as Mono
import Control.Category ((>>>))
import Data.Text.Prettyprint.Doc (Pretty(..))

import Muste.Tree
import qualified Muste.Tree.Internal as Tree
import Muste.Grammar
import qualified Muste.Grammar.Internal as Grammar
import Muste.AdjunctionTrees
import Muste.Prune
import Muste.Common.SQL (FromField, ToField)
import qualified Muste.Common.SQL as SQL

data LinToken = LinToken
  -- The path refers to the path in the 'TTree'
  { ltpath :: Path
  , ltlin :: String
  , _ltmatched :: Path
  }

deriving instance Show LinToken

deriving instance Generic LinToken

instance Binary LinToken where

instance Eq LinToken where
  (==) = (==) `on` ltlin

instance Ord LinToken where
  compare = compare `on` ltlin

newtype Linearization = Linearization { runLinearization :: [LinToken] }
  deriving
  ( Semigroup, Monoid
  , Ord, Eq, Binary
  , FromJSON, ToJSON
  )

stringRep ∷ Linearization → String
stringRep = otoList >>> fmap ltlin >>> unwords

deriving instance Show Linearization

instance Pretty Linearization where
  pretty = pretty . stringRep

-- This is not a valid show instance
-- instance Show Linearization where
--   show = show . stringRep

instance ToField Linearization where
  toField = SQL.toBlob

instance FromField Linearization where
  fromField = SQL.fromBlob

-- | Remember all 'AdjunctionTrees' in a certain 'PGF.Language' for a
-- certain 'Grammar'.
data Context = Context
  { ctxtGrammar :: Grammar
  , ctxtLang   :: PGF.Language
  , ctxtPrecomputed :: AdjunctionTrees
  }

instance FromJSON LinToken where
  parseJSON = withObject "LinToken" $ \v -> LinToken
    <$> v .: "path"
    <*> v .: "lin"
    <*> v .: "matched"

instance ToJSON LinToken where
  toJSON (LinToken path lin matched) = object
    [ "path"    .= path
    , "lin"     .= lin
    , "matched" .= matched
    ]

type instance Element Linearization = LinToken

deriving instance MonoFunctor Linearization

instance MonoFoldable Linearization where
  ofoldl'    f a (Linearization m) = ofoldl' f a m
  ofoldr     f a (Linearization m) = ofoldr f a m
  ofoldMap   f (Linearization m)   = ofoldMap f m
  ofoldr1Ex  f (Linearization m)   = ofoldr1Ex f m
  ofoldl1Ex' f (Linearization m)   = ofoldl1Ex' f m


instance MonoTraversable Linearization where
  otraverse f (Linearization m) = Linearization <$> otraverse f m

instance MonoPointed Linearization where
  opoint = Linearization . Mono.opoint

instance GrowingAppend Linearization where

instance SemiSequence Linearization where
  type Index Linearization = Int
  intersperse a = Linearization .  Mono.intersperse a . runLinearization
  reverse = Linearization . Mono.reverse . runLinearization
  find p = Mono.find p . runLinearization
  sortBy p = Linearization . Mono.sortBy p . runLinearization
  cons e = Linearization . Mono.cons e . runLinearization
  snoc xs e = Linearization . (`Mono.snoc` e) . runLinearization $ xs

instance IsSequence Linearization where

-- | Memoize all @AjdunctionTrees@ for a given grammar and language.
buildContext :: Grammar -> PGF.Language -> Context
buildContext grammar lang =
  Context grammar lang (getAdjunctionTrees grammar)

-- lin is the full linearization
-- Maybe fits better in the grammar.
-- | The 'linearizeTree' function linearizes a @TTree@ to a list of
-- tokens and paths to the nodes that create it
linearizeTree :: Context -> TTree -> Linearization
linearizeTree (Context grammar language _) ttree =
  let
    brackets = Grammar.brackets grammar language ttree
  in
    if not (Grammar.isEmptyGrammar grammar)
      && language `elem` PGF.languages (Grammar.pgf grammar)
      && not (null brackets)
    then bracketsToTuples ttree $ head brackets
    else Linearization [LinToken [] "?0" []]

-- | Given an identifier for a grammar, looks up that grammar and then
-- creates a mapping from all the languages in that grammar to their
-- respective 'Context's.
--
-- This method is unsafe and will throw if we can't find the
-- corresponding grammar.
langAndContext
  ∷ String -- ^ An identitfier for a grammar.  E.g. @novo_modo/Prima@.
  → Map String Context
langAndContext = readLangs . getGrammar
  where
  getGrammar ∷ String → Grammar
  getGrammar s = fromMaybe (err s) $ Grammar.lookupGrammar s
  err s = error $ printf errMsg s
  errMsg
    =  "Muste.Linearization.langAndContext: "
    <> "Couldn't find grammar corresponding for: %s"

-- | Given a grammar creates a mapping from all the languages in that
-- grammar to their respective 'Context's.
readLangs :: Grammar -> Map String Context
readLangs grammar
  = Map.fromList $ mkCtxt <$> PGF.languages (Grammar.pgf grammar)
  where
  mkCtxt lang = (PGF.showCId lang, buildContext grammar lang)


-- This part of the module knows about 'PGF' and maybe shouldn't.  The
-- problem is that 'LinToken' is introduced here and so cannot be
-- placed in 'Muste.Grammar.Internal' without having to move that as
-- well.

-- | Convert a 'PGF.BracketedString' to a list of string/path tuples.
bracketsToTuples :: TTree -> PGF.BracketedString -> Linearization
bracketsToTuples = deep
  where
  deep :: TTree -> PGF.BracketedString -> Linearization
  deep _     (PGF.Bracket _ _   _ _ _ []) = mempty
  -- Ordinary leaf
  deep ltree (PGF.Bracket _ fid _ _ _ [PGF.Leaf token]) =
    Linearization [LinToken (Tree.getPath ltree fid) token []]
  -- Meta leaf
  deep ltree (PGF.Bracket _ fid _ _ [PGF.EMeta id] _) =
    Linearization [LinToken (Tree.getPath ltree fid) ("?" ++ show id) []]
  -- In the middle of the tree
  deep ltree (PGF.Bracket _ fid _ _ _ bs) =
    broad ltree fid bs mempty
  deep _ _ = error "Muste.linearizeTree: Non-exhaustive pattern match"
  broad :: TTree -> Int -> [PGF.BracketedString] -> Linearization -> Linearization
  -- End of node siblings
  broad _     _   []                 ts = ts
  -- Syncategorial word
  broad ltree fid (PGF.Leaf token:bss) ts = Linearization (x:xs)
    where
    x = LinToken (Tree.getPath ltree fid) token []
    Linearization xs = broad ltree fid bss ts
  -- In the middle of the nodes
  broad ltree fid (bs:bss)
    ts = deep ltree bs <> broad ltree fid bss ts

-- | @'matchTk' t0 t1 tk@ checks if a 'LinToken' matches both trees
-- @t0@ and @t1@ and creates a new 'LinToken' indicating this.
matchTk :: TTree -> TTree -> LinToken -> LinToken
matchTk srcTree trgTree (LinToken path lin _)
    = LinToken path lin (matched path srcTree trgTree)

-- | Checks if a linearization token matches in both trees.  If they
-- don't match, then the empty path is returned.
matched :: Path -> TTree -> TTree -> Path
matched p t1 t2 =
  if Tree.selectNode t1 p == Tree.selectNode t2 p
  then p
  else mempty

mkLin
  :: Context
  -> TTree
  -> TTree
  -> TTree -- ^ The actual tree to linearize
  -> Linearization
mkLin ctxt srcTree trgTree tree
  = Linearization $ matchTk srcTree trgTree <$> xs
  where
    (Linearization xs) = linearizeTree ctxt tree

-- | @'sameOrder' xs ys@ checks to see if the tokens in @xs@ occurs in
-- the same sequence in @ys@.
sameOrder :: Linearization -> Linearization -> Bool
sameOrder (Linearization xs) (Linearization ys) = sameOrder' xs ys

-- If we were feeling fancy we might be able to generalize this from
-- '[]' to any 'Traversable'.
-- | @'sameOrder'' xs ys@ checks to see if the elements in @xs@ occurs
-- in the same sequence in @ys@.
sameOrder' :: Eq a => [a] -> [a] -> Bool
sameOrder' [] _ = True
sameOrder' _ [] = False
sameOrder' (x:xs) yss@(y:ys)
  | x == y    = sameOrder' xs ys
  | otherwise = sameOrder' xs yss

disambiguate ∷ Context → Linearization → [TTree]
disambiguate ctxt = stringRep >>> parse
  where
  parse ∷ String → [TTree]
  parse = Grammar.parseSentence (ctxtGrammar ctxt) (ctxtLang ctxt)
