{- | This Module is the internal implementation behind the module 'Muste.Grammar' -}
module Muste.Grammar.Internal
  -- ( wildCard
  -- , emptyGrammar
  -- , isEmptyPGF
  -- , isEmptyGrammar
  -- , getFunType
  -- , getRuleName
  -- , pgfToGrammar
  where

import Prelude hiding (id)
import PGF
import PGF.Internal hiding (funs, cats)
import Data.List
import Muste.Feat (Grammar(Grammar), FunType(Fun,NoType), Rule(Function), mkFEAT)
-- import Muste.Feat hiding (startcat, pgf)
import qualified Muste.Feat as Feat

wildCard :: String
wildCard = "*empty*"

-- | Constant for an empty 'Grammar' in line with 'emptyPGF'
emptyGrammar :: Grammar
emptyGrammar = Grammar wildCard [] [] emptyPGF Feat.emptyFeat

-- | Predicate to check if a PGF is empty, i.e. when the absname is
-- wildCId
isEmptyPGF :: PGF -> Bool
isEmptyPGF pgf = absname pgf == wildCId

-- | Predicate to check if a Grammar is empty, i.e. when the startcat
-- is wildCId and pgf is empty
isEmptyGrammar :: Grammar -> Bool
isEmptyGrammar grammar = Feat.startcat grammar == wildCard && isEmptyPGF (Feat.pgf grammar)
  

-- | The function 'getFunTypeWithGrammar' extracts the function type from a Grammar given a function name
getFunType :: Grammar -> String -> FunType
getFunType g id =
  let
    rules = filter (\r -> getRuleName r == id) $ Feat.getAllRules g
  in
    if not $ null rules then Feat.getRuleType $ head rules else NoType

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
      funs = functions pgf
      -- Get their types
      funtypes = map (getFunTypeWithPGF pgf) funs
      -- Combine to a rule
      rules = zipWith Function (map showCId funs) funtypes
      -- Split in lexical and syntactical rules
      (lexrules,synrules) = partition (\r -> case r of { Function _ (Fun _ []) -> True ; _ -> False } ) rules
      -- Get the startcat from the PGF
      (_, startcat, _) = unType (startCat pgf)
    in
      Grammar (showCId startcat) synrules lexrules pgf (mkFEAT (Grammar (showCId startcat) synrules lexrules pgf Feat.emptyFeat))
  where
    getFunTypeWithPGF :: PGF -> CId -> FunType
    getFunTypeWithPGF grammar id
      | isEmptyPGF grammar = NoType -- Empty grammar
      | otherwise =
        let
          typ = functionType grammar id
        in
          case typ of {
            Nothing -> NoType ; -- No type found in grammar
            Just t ->
            let
              (hypos,typeid,_exprs) = unType t
              cats = map (\(_,_,DTyp _ cat _) -> cat) hypos
            in
              Fun (showCId typeid) (map showCId cats)
            }
