{-# LANGUAGE FlexibleInstances #-}
module Grammar where
import PGF
import PGF.Internal
import Data.Maybe

-- first CId is the the result category and [CId] are the parameter categories
data FunType = Fun CId [CId]

-- CId is the function name
data Rule = Function CId FunType

data Grammar = Grammar {
  startcat :: CId,
  rules :: [Rule]
  }

instance Show Grammar where
  show (Grammar startcat rules) =
    "Startcat: " ++ show startcat ++ "\nRules:\n " ++
    (unwords $ map show rules)
    
instance Show FunType where
  show (Fun cat []) =
    "(" ++ show cat ++ ")"
  show (Fun cat cats) =
    "(" ++ (foldl (\a -> \b -> a ++ " -> " ++ (show b)) (show $ head cats) (tail cats) ++ " -> " ++ show cat) ++ ")"

-- A funtype is in the Read class
instance Read FunType where
  readsPrec _ sType =
    let
      readType :: String -> String -> ([String],String)
      -- Skip a ( at the start
      readType cat ('(':rest) = readType cat rest
      -- A ) as the end marker
      readType cat (')':rest) = ([cat],rest)
      -- An arrow -> between the categories
      readType cat (' ':'-':'>':' ':rest) =
        let
          result = readType "" rest
        in
        (fst result ++ [cat],snd result)
        -- Completely read a category -- maybe better use read :: CId ??? 
      readType cat (c:rest) =
        readType (cat ++ [c]) rest
      readType cat [] = ([cat],[])
      result = readType "" sType
      cats = reverse $ fst result
    in
      [((Fun (mkCId (last cats)) (map mkCId (init cats))),snd result)]

instance Eq FunType where
  (==) (Fun id1 pre1) (Fun id2 pre2) = (id1 == id2) && (pre1 == pre2) 

instance Show Rule where
  show (Function name funtype) =
    show name ++ " : " ++ show funtype ;

showType :: Maybe Type -> String
showType Nothing = "NoType"
showType (Just (DTyp hypos id exprs)) = show id

-- instance Show Grammar where
--   show g = unwords $ map show g
       
getFunType :: PGF -> CId -> FunType
getFunType grammar id =
  let
    typ = fromJust $ functionType grammar id -- Here is some uncertainty from the grammar but we just assume there will always be a type
    (hypos,typeid,exprs) = unType typ
    cats = (map (\(_,_,DTyp _ cat _) -> cat) hypos)
  in
    (Fun typeid cats) ;

getFunCat :: FunType -> CId
getFunCat (Fun cat _) = cat

getRuleCat :: Rule -> CId
getRuleCat (Function _ funType) = getFunCat funType 

pgfToGrammar :: PGF -> Grammar
pgfToGrammar pgf =
  let
--    cats = categories pgf
    funs = functions pgf
    funtypes = map (getFunType pgf) funs
    zipped = zip funs funtypes
    rules = map (\(id,typ) -> Function id typ) zipped
    (_, startcat, _) = unType (startCat pgf)
  in
    Grammar startcat rules


