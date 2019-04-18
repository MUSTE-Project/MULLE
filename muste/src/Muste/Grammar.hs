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

module Muste.Grammar
  ( Grammar(..)
  , Rule(..)
  , isEmptyGrammar
  , getAllRules
  , getRuleType
  , brackets
  , parseTTree
  , parseSentence
  , getMetas
  , getFunctions
  , getFunNames
  , hole
  , bracketsToTuples
  , readGrammar
  ) where

import Control.Category ((>>>))
import GHC.Generics (Generic)

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

readGrammar :: Text -> IO Grammar
readGrammar p = do g <- PGF.readPGF $ Text.unpack p
                   return $ pgfToGrammar g

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
