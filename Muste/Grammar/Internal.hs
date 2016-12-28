{-# LANGUAGE FlexibleInstances #-}
{- | This Module is the internal implementation behind the module 'Muste.Grammar' -}
module Muste.Grammar.Internal where
import PGF
import PGF.Internal
import Data.Maybe
import Data.Set (Set(..),fromList)
import Test.QuickCheck

-- | Type 'FunType' consists of a CId that is the the result category and [CId] are the parameter categories
data FunType = Fun CId [CId] | NoType deriving (Ord,Eq)

-- | A 'FunType' is in the Show class
instance Show FunType where
  show (Fun cat []) =
    "(" ++ show cat ++ ")"
  show (Fun cat cats) =
    "(" ++ (foldl (\a b -> a ++ " -> " ++ show b) (show $ head cats) (tail cats) ++ " -> " ++ show cat) ++ ")"
  show NoType = "()"

-- | A 'FunType' is in the Read class
instance Read FunType where
  readsPrec _ sType =
    let
      readType :: String -> ([CId],String)
      readType (' ':rest) = readType rest
      readType ('(':rest) = readType rest
      readType (')':rest) = ([],rest)
      readType ('-':'>':rest) =
        let
          result = readType rest
        in
          result
      readType "" = ([],"")
      readType rest =
        let
          result = readId rest
        in
          case result of {
            Just r -> let more = readType $ snd r in (fst r:fst more, snd more) ;
            _ -> ([],rest)
            }
      result = readType sType
      cats = fst result
    in
      case cats of {
        [] -> [(NoType,snd result)] ; -- Empty Result
        _ ->[(Fun (last cats) (init cats),snd result)] }

-- A 'FunType' can be generated randomly
instance Arbitrary FunType where
  arbitrary =
    frequency [(9,newFun),(1,return NoType)]
    where
      newFun = do
        let ids = ['A'..'Z']
        cat <- elements ids
        cats <- listOf $ elements ids
        return $ Fun (mkCId [cat]) (map (mkCId . charToString) cats)
      charToString c = [c]

-- | Type 'Rule' consists of a CId as the function name and a 'FunType' as the Type
data Rule = Function CId FunType deriving (Ord,Eq)

-- | A 'Rule' is member of the Show class
instance Show Rule where
  show (Function name funtype) =
    show name ++ " : " ++ show funtype ;

-- | Type 'Grammar' consists of a start categorie and a list of rules
data Grammar = Grammar {
  startcat :: CId,
  rules :: [Rule],
  pgf :: PGF
  }

-- | A 'Grammar' is in the EQ class
instance Eq Grammar where
  (==) g1@(Grammar s1 rs1 pgf1) g2@(Grammar s2 rs2 pgf2) =
    s1 == s2 &&
    rs1 == rs2
    -- pgf1 == pgf2 -- To be fixed somehow
    
-- | A 'Grammar' is in the Show class
instance Show Grammar where
  show (Grammar startcat rules _) =
    "Startcat: " ++ show startcat ++ "\nRules: \n" ++
    unwords (map (\r -> "\t" ++ show r ++ "\n") rules)

-- | Constant for an empty 'Grammar' in line with 'emptyPGF'
emptyGrammar = Grammar wildCId [] emptyPGF

-- | Predicate to check if a PGF is empty, i.e. when the absname is wildCId
isEmptyPGF pgf = absname pgf == wildCId

-- | Predicate to check if a Grammar is empty, i.e. when the startcat is wildCId and pgf is empty
isEmptyGrammar grammar = startcat grammar == wildCId && isEmptyPGF (pgf grammar)

-- | The function 'readId' is a helper to read a 'FunType'
readId :: String -> Maybe (CId,String)
-- Workaround for ? (used for unknown types)
readId ('?':rest) =
  let
    tmp = readId rest
  in
    case tmp of {
      Nothing -> Just (mkCId "?","") ;
      Just (id,rst) -> Just (mkCId  ("?" ++ show id),rst)
      }
readId str =
  let
    result = reads str
  in
    if null result then Nothing else Just $ head result


-- | The function 'getFunType' extracts the function type from a grammar given a function name
getFunType :: PGF -> CId -> FunType
getFunType grammar id
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
          Fun typeid cats
        }

-- | The function 'getFunCat' extracts the result category from a function type
getFunCat :: FunType -> CId
getFunCat (Fun cat _) = cat
getFunCat _ = wildCId

-- | The function 'getRuleCat' extracts the result category of a rule
getRuleCat :: Rule -> CId
getRuleCat (Function _ funType) = getFunCat funType 

-- | The function 'getRules' finds all rules in grammar that have a certain result category
getRules :: Grammar -> [CId] -> Set Rule
getRules grammar cats =
    let
      rs = rules grammar
    in
      -- Convert rules from GF format to our only one
      fromList $ concatMap (\c -> filter (\(Function _ (Fun fcat _)) -> fcat == c ) rs) cats

-- | The function 'pgfToGrammar' transforms a PGF grammar to a simpler grammar data structure
pgfToGrammar :: PGF -> Grammar
pgfToGrammar pgf 
  | isEmptyPGF pgf = emptyGrammar
  | otherwise =
    let
      -- Get function names
      funs = functions pgf
      -- Get their types
      funtypes = map (getFunType pgf) funs
      -- Combine to a rule
      rules = zipWith Function funs funtypes
      -- Get the startcat from the PGF
      (_, startcat, _) = unType (startCat pgf)
    in
      Grammar startcat rules pgf


