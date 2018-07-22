{-# language OverloadedStrings, TypeApplications #-}
{- | This Module is the internal implementation behind the module 'Muste.Grammar' -}
module Muste.Grammar.Internal
  ( Grammar(..)
  , Rule(..)
  , pgfToGrammar
  , isEmptyGrammar
  , getFunType
  , getAllRules
  , getRuleType
  , readPGF
  , brackets
  )  where

import Prelude hiding (id)

-- This might be the only place we should know of PGF
import qualified PGF
import PGF.Internal as PGF hiding (funs, cats)
import Data.List
import Data.Text.Prettyprint.Doc (Pretty(..))
import qualified Data.Text.Prettyprint.Doc as Doc
import Text.Printf

import Muste.Common
import Muste.Tree

-- | Type 'Rule' consists of a 'String' representing the function name
-- and a 'FunType' representing its type.
data Rule = Function String FunType deriving (Ord,Eq,Show,Read)

-- | Type 'Grammar' consists of a start category and a list of rules.
data Grammar = Grammar {
  startcat :: String,
  synrules :: [Rule],
  lexrules :: [Rule],
  pgf :: PGF
  }

instance Pretty Grammar where
  pretty (Grammar sCat srules lrules _) = Doc.sep
    [ p "Startcat: %s" (show sCat)
    , p "Syntactic Rules: %s" (s srules)
    , p "Lexical Rules: %s" (s lrules)
    ]
    where
    s = unwords . (map (\r -> "\t" ++ show r ++ "\n"))
    p :: String -> String -> Doc.Doc ann
    p frmt s = Doc.pretty @String $ printf frmt s

-- | Rename GF abstract syntax tree (from PGF)
type GFAbsTree = PGF.Tree

-- | Creates a GF abstract syntax Tree from a generic tree
ttreeToGFAbsTree :: TTree -> GFAbsTree
ttreeToGFAbsTree tree =
  let
    loop :: [TTree] -> Int -> (Int,[GFAbsTree])
    loop [] id = (id,[])
    loop (t:ts) id =
      let
        (nid,nt) = convert t id
        (fid,nts) = loop ts nid
      in
        (fid,nt:nts)
    convert :: TTree -> Int -> (Int,GFAbsTree)
    convert (TMeta _) id = (id + 1, mkMeta id)
    convert (TNode name _ ns) id =
      let
        (nid,nts) = loop ns id
      in
        if name == wildCard then (nid,mkApp PGF.wildCId nts) else (nid,mkApp (PGF.mkCId name) nts)
  in
    snd $ convert tree 0

-- | The function 'getRules' returns the union of syntactic and lexical rules of a grammar
getAllRules :: Grammar -> [Rule]
getAllRules g = union (synrules g) (lexrules g)

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

-- | Converts a @.pgf@ file to a 'Grammar'.
readPGF
  :: FilePath -- ^ Path to the grammar.
  -> IO Grammar
readPGF grammarName = pgfToGrammar <$> PGF.readPGF grammarName

brackets :: Grammar -> PGF.Language -> TTree -> [PGF.BracketedString]
brackets grammar language ttree
  = PGF.bracketedLinearize (pgf grammar) language (ttreeToGFAbsTree ttree) :: [PGF.BracketedString]
