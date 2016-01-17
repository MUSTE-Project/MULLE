{-# LANGUAGE FlexibleInstances #-}
module Grammar where
import PGF
import PGF.Internal
import Data.Maybe

-- first CId is the the result category and [CId] are the parameter categories
data FunType = Fun CId [CId]

-- CId is the function name
data Rule = Function CId (Maybe FunType)

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
    show cat
  show (Fun cat cats) =
    foldl (\a -> \b -> a ++ " -> " ++ (show b)) (show $ head cats) (tail cats) ++ " -> " ++ show cat
instance Eq FunType where
  (==) (Fun id1 pre1) (Fun id2 pre2) = (id1 == id2) && (pre1 == pre2) 
instance Show Rule where
  show (Function name funtype) =
    show name ++ " : " ++ show funtype ;
    
-- instance Show Grammar where
--   show g = unwords $ map show g
       
getFunType :: PGF -> CId -> Maybe FunType
getFunType grammar id =
  let
    typ = functionType grammar id
  in
    do
      case typ of {
        (Just t) -> let
                (hypos,typeid,exprs) = unType $ fromJust typ
                cats = (map (\(_,_,DTyp _ cat _) -> cat) hypos)
                in
                  Just (Fun typeid cats) ;
        _ -> Nothing
        } ;

getFunCat :: FunType -> CId
getFunCat (Fun cat _) = cat

getRuleCat :: Rule -> Maybe CId
getRuleCat (Function _ (Just funType)) = Just $ getFunCat funType 
getRuleCat _ = Nothing

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


