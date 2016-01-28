{-# LANGUAGE FlexibleInstances #-}
module Grammar where
import PGF
import PGF.Internal
import Data.Maybe

-- first CId is the the result category and [CId] are the parameter categories
data FunType = Fun CId [CId] | NoType

-- CId is the function name
data Rule = Function CId FunType

-- A Grammar consists of a start categorie and a list of rules
data Grammar = Grammar {
  startcat :: CId,
  rules :: [Rule]
  }

-- A grammar is in the Show class
instance Show Grammar where
  show (Grammar startcat rules) =
    "Startcat: " ++ show startcat ++ "\nRules:\n " ++
    (unwords $ map show rules)

-- A funtype is in the Show class
instance Show FunType where
  show (Fun cat []) =
    "(" ++ show cat ++ ")"
  show (Fun cat cats) =
    "(" ++ (foldl (\a -> \b -> a ++ " -> " ++ (show b)) (show $ head cats) (tail cats) ++ " -> " ++ show cat) ++ ")"
  show (NoType) = "()"

readId :: String -> Maybe (CId,String)
readId str =
  let
    result = readsPrec 0 str
  in
    if result == [] then Nothing else Just $ head result
  
-- A funtype is in the Read class
instance Read FunType where
  readsPrec _ sType =
    let
      readType :: String -> ([CId],String)
      readType ('(':rest) = readType rest
      readType (')':rest) = ([],rest)
      readType (' ':'-':'>':' ':rest) =
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

-- A funtype is a member of Eq class
{-
  Function types are equal if all hypothesises and the resulting category are equal
-}
instance Eq FunType where
  (==) (Fun id1 pre1) (Fun id2 pre2) = (id1 == id2) && (pre1 == pre2) 

-- A rule is member of the Show class
instance Show Rule where
  show (Function name funtype) =
    show name ++ " : " ++ show funtype ;

-- Given a function name extracts its type from a grammar
getFunType :: PGF -> CId -> FunType
getFunType grammar id =
  let
    typ = fromJust $ functionType grammar id -- Here is some uncertainty from the grammar but we just assume there will always be a type
    (hypos,typeid,exprs) = unType typ
    cats = (map (\(_,_,DTyp _ cat _) -> cat) hypos)
  in
    (Fun typeid cats) ;

-- Extracts the result category from a function type
getFunCat :: FunType -> CId
getFunCat (Fun cat _) = cat

-- Extracts the result category of a rule
getRuleCat :: Rule -> CId
getRuleCat (Function _ funType) = getFunCat funType 

-- Transform a PGF grammar to a simpler data structure
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
    Grammar startcat rules


