{-# LANGUAGE FlexibleInstances #-}
{- | This Module gives an abstraction from the PGF format provided by GF -}
module Muste.Grammar where
import PGF
import PGF.Internal
import Data.Maybe

-- | Type 'FunType' consists of a CId that is the the result category and [CId] are the parameter categories
data FunType = Fun CId [CId] | NoType deriving (Ord,Eq)

-- | Type 'Rule' consists of a CId as the function name and a 'FunType' as the Type
data Rule = Function CId FunType deriving (Ord,Eq)

-- | Type 'Grammar' consists of a start categorie and a list of rules
data Grammar = Grammar {
  startcat :: CId,
  rules :: [Rule],
  pgf :: PGF
  }


-- | A 'FunType' is in the Show class
instance Show FunType where
  show (Fun cat []) =
    "(" ++ show cat ++ ")"
  show (Fun cat cats) =
    "(" ++ (foldl (\a -> \b -> a ++ " -> " ++ (show b)) (show $ head cats) (tail cats) ++ " -> " ++ show cat) ++ ")"
  show (NoType) = "()"

-- | A 'Rule' is member of the Show class
instance Show Rule where
  show (Function name funtype) =
    show name ++ " : " ++ show funtype ;

-- | A 'Grammar' is in the Show class
instance Show Grammar where
  show (Grammar startcat rules _) =
    "Startcat: " ++ show startcat ++ "\nRules: \n" ++
    (unwords $ map (\r -> "\t" ++ (show r) ++ "\n") rules)

  
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
          (fst result, snd result)
      readType "" = ([],"")
      readType rest =
        let
          result = readId rest
        in
          case result of {
            Just r -> let more = readType $ snd r in ((fst r):(fst more), snd more) ;
            _ -> ([],rest)
            }
      result = readType sType
      cats = fst result
    in
      [((Fun (last cats) (init cats)),snd result)]

-- The function 'readId' is a helper to read a 'FunType'
readId :: String -> Maybe (CId,String)
-- Workaround for ? (used for unknown types)
readId ('?':rest) =
  let
    tmp = readId rest
  in
    case tmp of {
      Nothing -> Just ((mkCId "?"),"") ;
      Just (id,rst) -> Just (mkCId  ("?" ++ (show id)),rst)
      }
readId str =
  let
    result = readsPrec 0 str
  in
    if result == [] then Nothing else Just $ head result


-- | The function 'getFunType' extracts the function type from a grammar given a function name
getFunType :: PGF -> CId -> FunType
getFunType grammar id =
  let
    typ = fromJust $ functionType grammar id -- Here is some uncertainty from the grammar but we just assume there will always be a type
    (hypos,typeid,exprs) = unType typ
    cats = (map (\(_,_,DTyp _ cat _) -> cat) hypos)
  in
    (Fun typeid cats) ;

-- | The function 'getFunCat' extracts the result category from a function type
getFunCat :: FunType -> CId
getFunCat (Fun cat _) = cat

-- | The function 'getRuleCat' extracts the result category of a rule
getRuleCat :: Rule -> CId
getRuleCat (Function _ funType) = getFunCat funType 

-- | The function 'pgfToGrammar' transforms a PGF grammar to a simpler grammar data structure
pgfToGrammar :: PGF -> Grammar
pgfToGrammar pgf =
  let
    -- Get function names
    funs = functions pgf
    -- Get their types
    funtypes = map (getFunType pgf) funs
    -- Combine to a rule
    rules = map (\(id,typ) -> Function id typ) (zip funs funtypes)
    -- Get the startcat from the PGF
    (_, startcat, _) = unType (startCat pgf)
  in
    Grammar startcat rules pgf


