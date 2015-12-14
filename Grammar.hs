module Grammar where
import PGF
import PGF.Internal
import Data.Maybe

type FunType = [CId]

getfuntype :: PGF -> CId -> FunType
getfuntype grammar id =
  let
    typ = functionType grammar id
    (hypos,typeid,exprs) = unType $ fromJust typ
    cats = (map (\(_,_,DTyp _ cat _) -> cat) hypos) ++ [typeid]
  in
    do      
      cats

showfuntype :: FunType -> String
showfuntype cats =
  foldl (\a -> \b -> a ++ " -> " ++ (show b)) (show $ head cats) (tail cats)
