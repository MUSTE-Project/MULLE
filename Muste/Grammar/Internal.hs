{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{- | This Module is the internal implementation behind the module 'Muste.Grammar' -}
module Muste.Grammar.Internal where
import PGF hiding (parse)
import PGF.Internal hiding (nub)
import Data.Maybe
import Data.Set (Set(..),fromList)
import Test.QuickCheck
-- import Text.Parsec
import Data.Char
import Data.List

wildCard = "*empty*"

-- | Type 'FunType' consists of a String that is the the result category and [String] are the parameter categories
data FunType = Fun String [String] | NoType deriving (Ord,Eq,Show,Read)

-- A 'FunType' can be generated randomly
instance Arbitrary FunType where
  arbitrary =
    frequency [(9,sized newFun),(1,return NoType)]
    where
      newFun len = do
        let ids = ['A'..'E']
        cat <- elements ids
        cats <- resize len $ listOf1 $ elements ids
        return $ Fun [cat] (map charToString cats)
      charToString c = [c]

-- | Type 'Rule' consists of a String as the function name and a 'FunType' as the Type
data Rule = Function String FunType deriving (Ord,Eq,Show,Read)

-- A 'FunType' can be generated randomly
instance Arbitrary Rule where
  arbitrary =
    do
      let ids = ['f'..'z']
      id <- elements ids
      funtype <- arbitrary 
      return $ Function [id] funtype
      
-- | Type 'Grammar' consists of a start categorie and a list of rules
data Grammar = Grammar {
  startcat :: String,
  synrules :: [Rule],
  lexrules :: [Rule],
  pgf :: PGF
  }

instance Arbitrary Grammar where
  arbitrary =
    do
      -- generate list of rules
      genrules <- fmap (filter (\f -> case f of { (Function _ NoType) -> False ; _ -> True })) $ listOf1 (resize 3 arbitrary)
      let filterrules = nubBy (\(Function id1 _) (Function id2 _) -> id1 == id2 ) genrules
      let rules = if not $ null filterrules then filterrules else [(Function "f" (Fun "A" ["A"]))]
      -- select start category
      let startCat = getRuleCat $ head rules
      -- get all the cats on the rhss
      let allCats = nub $ concat $ map (\(Function _ (Fun _ cats)) -> cats) rules -- Problematic
      let lexRules = map (\c -> Function (map toLower c) (Fun c [])) allCats
      return $ Grammar startCat rules lexRules emptyPGF
      
-- | A 'Grammar' is in the EQ class
instance Eq Grammar where
  (==) g1@(Grammar s1 rs1 ls1 pgf1) g2@(Grammar s2 rs2 ls2 pgf2) =
    s1 == s2 &&
    rs1 == rs2 &&
    ls1 == ls2
    -- pgf1 == pgf2 -- To be fixed somehow
    
-- | A 'Grammar' is in the Show class
instance Show Grammar where
  show (Grammar startcat srules lrules _) =
    "Startcat: " ++ show startcat ++ "\nSyntactic Rules: \n" ++
    unwords (map (\r -> "\t" ++ show r ++ "\n") srules)
    ++ "\nLexical Rules: \n" ++
    unwords (map (\r -> "\t" ++ show r ++ "\n") lrules)

-- | Constant for an empty 'Grammar' in line with 'emptyPGF'
emptyGrammar = Grammar wildCard [] [] emptyPGF

-- | Predicate to check if a PGF is empty, i.e. when the absname is wildCId
isEmptyPGF pgf = absname pgf == wildCId

-- | Predicate to check if a Grammar is empty, i.e. when the startcat is wildCId and pgf is empty
isEmptyGrammar grammar = startcat grammar == wildCard && isEmptyPGF (pgf grammar)
  
-- | The function 'getFunTypeWithPGF' extracts the function type from a PGF given a function name
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
          (hypos,typeid,exprs) = unType t
          cats = map (\(_,_,DTyp _ cat _) -> cat) hypos
        in
          Fun (showCId typeid) (map showCId cats)
        }

-- | The function 'getFunTypeWithGrammar' extracts the function type from a Grammar given a function name
getFunTypeWithGrammar :: Grammar -> String -> FunType
getFunTypeWithGrammar g id =
  let
    rules = filter (\r -> getRuleName r == id) $ getAllRules g
  in
    if not $ null rules then getRuleType $ head rules else NoType

-- | The function 'getFunCat' extracts the result category from a function type
getFunCat :: FunType -> String
getFunCat (Fun cat _) = cat
getFunCat _ = wildCard

-- | The function 'getRuleCat' extracts the result category of a rule
getRuleCat :: Rule -> String
getRuleCat (Function _ funType) = getFunCat funType

-- | The function 'getRuleName' extracts the name of a rule
getRuleName :: Rule -> String
getRuleName (Function name _) = name

-- | The function 'getRuleType' extracts the full type of a rule
getRuleType :: Rule -> FunType
getRuleType (Function _ funType) = funType

-- | The function 'getRules' finds all rules in grammar that have a certain result category
getRulesSet :: [Rule] -> [String] -> Set Rule
getRulesSet rules cats =
  -- Convert rules from GF format to our only one
  fromList $ concatMap (\c -> filter (\f -> case f of { (Function _ (Fun fcat _)) -> fcat == c ; _ -> False }) rules) cats

-- | The function 'getRules' finds all rules in grammar that have a certain result category
getRulesList :: [Rule] -> [String] -> [Rule]
getRulesList rules cats =
  -- Convert rules from GF format to our only one
  concatMap (\c -> filter (\(Function _ (Fun fcat _)) -> fcat == c ) rules) cats

-- | The function 'getRules' returns the union of syntactic and lexical rules of a grammar
getAllRules :: Grammar -> [Rule]
getAllRules g = union (synrules g) (lexrules g)

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
      Grammar (showCId startcat) synrules lexrules pgf
