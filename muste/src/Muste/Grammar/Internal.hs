{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
{-# language OverloadedStrings, TypeApplications, UnicodeSyntax #-}
{- | This Module is the internal implementation behind the module 'Muste.Grammar' -}
module Muste.Grammar.Internal
  ( Grammar(..)
  , Rule(..)
  -- Used internally
  , isEmptyGrammar
  , getAllRules
  , getRuleType
  , brackets
  , parseTTree
  , lookupGrammar
  , lookupGrammarM
  , parseGrammar
  , parseSentence
  , getMetas
  , getFunctions
  ) where

import Prelude ()
import Muste.Prelude

import Data.Map (Map)
import qualified Data.Map as Map
import Data.ByteString as SB (ByteString)
import qualified Data.ByteString.Lazy as LB
-- This might be the only place we should know of PGF
import qualified PGF
  ( Tree, wildCId, functions
  , showCId, startCat, functionType, parsePGF
  , bracketedLinearize, parse
  )
import PGF.Internal as PGF hiding (funs, cats)
import Data.List (union, partition)
import Data.Text.Prettyprint.Doc (Pretty(..))
import qualified Data.Text.Prettyprint.Doc as Doc
import Control.DeepSeq
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet

import qualified Muste.Grammar.Grammars as Grammars
import Muste.Common
import Muste.Tree
import qualified Muste.Tree.Internal as Tree

-- | Type 'Rule' consists of a 'String' representing the function name
-- and a 'FunType' representing its type.
data Rule = Function String FunType deriving (Ord,Eq,Show,Read)

-- | Type 'Grammar' consists of a start category and a list of rules.
data Grammar = Grammar
  { startcat :: String
  , synrules :: [Rule]
  , lexrules :: [Rule]
  , pgf :: PGF
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

-- | The function 'getRules' returns the union of syntactic and lexical rules of a grammar
getAllRules :: Grammar -> [Rule]
getAllRules g = synrules g `union` lexrules g

-- | The function 'getRuleType' extracts the full type of a rule
getRuleType :: Rule -> FunType
getRuleType (Function _ funType) = funType

-- | Constant for an empty 'Grammar' in line with 'emptyPGF'
emptyGrammar :: Grammar
emptyGrammar = Grammar wildCard [] [] emptyPGF

-- | Predicate to check if a PGF is empty, i.e. when the absname is
-- PGF.wildCId
isEmptyPGF :: PGF -> Bool
isEmptyPGF pgf = absname pgf == PGF.wildCId

-- | Predicate to check if a Grammar is empty, i.e. when the startcat
-- is PGF.wildCId and pgf is empty
isEmptyGrammar :: Grammar -> Bool
isEmptyGrammar grammar = startcat grammar == wildCard && isEmptyPGF (pgf grammar)

-- | The function 'getFunTypeWithGrammar' extracts the function type from a Grammar given a function name
getFunType :: Grammar -> String -> FunType
getFunType g id =
  let
    rules = filter (\r -> getRuleName r == id) $ getAllRules g
  in
    if not $ null rules then getRuleType $ head rules else NoType

-- | The function 'getRuleName' extracts the name of a rule
getRuleName :: Rule -> String
getRuleName (Function name _) = name

-- | The function 'pgfToGrammar' transforms a PGF grammar to a simpler grammar data structure
pgfToGrammar :: PGF -> Grammar
pgfToGrammar pgf 
  | isEmptyPGF pgf = emptyGrammar
  | otherwise =
    let
      -- Get function names
      funs = PGF.functions pgf
      -- Get their types
      funtypes = map (getFunTypeWithPGF pgf) funs
      -- Combine to a rule
      rules = zipWith Function (map PGF.showCId funs) funtypes
      -- Split in lexical and syntactical rules
      (lexrules,synrules) = partition (\r -> case r of { Function _ (Fun _ []) -> True ; _ -> False } ) rules
      -- Get the startcat from the PGF
      (_, startcat, _) = unType (PGF.startCat pgf)
    in
      Grammar (PGF.showCId startcat) synrules lexrules pgf
  where
    getFunTypeWithPGF :: PGF -> CId -> FunType
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
              (hypos,typeid,_exprs) = unType t
              cats = map (\(_,_,DTyp _ cat _) -> cat) hypos
            in
              Fun (PGF.showCId typeid) (map PGF.showCId cats)
            }

-- | Although the parameter to 'parseGrammar' is a lazy stream it's
-- contents will be forced.
parseGrammar
  :: LB.ByteString -- ^ The grammar in binary format.
  -> Grammar
-- 'PGF.parsePGF' seems to consume the lazy bytestring in an
-- inconvenient manner.  The problem does not appear to be there if we
-- force the bytestring.
parseGrammar = pgfToGrammar . PGF.parsePGF . force

brackets :: Grammar -> PGF.Language -> TTree -> [PGF.BracketedString]
brackets grammar language ttree
  = PGF.bracketedLinearize (pgf grammar) language (Tree.toGfTree ttree)

parseTTree :: Grammar -> String -> TTree
parseTTree g = fromGfTree g . read

-- | The function 'fromGfTree' creates a 'TTree' from an
-- 'PGF.Tree' and a 'Grammar'. Othewise similar to
-- 'fromGfTreeWithPGF'
fromGfTree :: Grammar -> PGF.Tree -> TTree
fromGfTree g (EFun f) =
  let
    typ = getFunType g (PGF.showCId f)
  in
    TNode (PGF.showCId f) typ []
fromGfTree g (EApp e1 e2) =
  let
    (TNode name typ sts) = fromGfTree g e1
    st2 = fromGfTree g e2
  in
    TNode name typ (sts ++ [st2])
fromGfTree _ _ = TMeta wildCard

grammars :: Map Text Grammar
grammars = Map.fromList (uncurry grm <$> Grammars.grammars)
  where
  grm :: Text -> SB.ByteString -> (Text, Grammar)
  grm idf pgf = (idf, parseGrammar $ LB.fromStrict pgf)

-- | Lookup a grammar amongst the ones that we know of.  The grammars
-- that we know of are the ones linked against this binary at
-- compile-time.  See 'Muste.Grammar.Grammars.grammars'.
lookupGrammar ∷ Text → Maybe Grammar
lookupGrammar s = Map.lookup s grammars

-- | Lookup a grammar in some fallible monad.  A lifted version of
-- 'lookupGrammar'.
lookupGrammarM ∷ MonadFail m ⇒ String → Text → m Grammar
lookupGrammarM err = lookupGrammar >>> maybeFail err

-- | Parses a linearized sentence.  Essentially a wrapper around
-- 'PGF.parse'.
parseSentence ∷ Grammar → Language → String → [TTree]
parseSentence grammar lang = pgfIfy >>> fmap musteIfy
  where
  pgfIfy ∷ String → [PGF.Tree]
  pgfIfy = PGF.parse (pgf grammar) lang (PGF.startCat p)
  musteIfy ∷ PGF.Tree → TTree
  musteIfy = fromGfTree grammar
  p ∷ PGF.PGF
  p = pgf grammar

-- | Returns a bag of all meta-variables in a tree.
getMetas :: TTree -> MultiSet Category
getMetas = \case
  TMeta cat → MultiSet.singleton cat
  TNode _ _ ts → mconcat $ getMetas <$> ts

-- | Returns a bag of all functions in a tree.
getFunctions :: TTree -> MultiSet Rule
getFunctions = Tree.foldMapTTree step
  where
  step fun typ = MultiSet.singleton $ Function fun typ
