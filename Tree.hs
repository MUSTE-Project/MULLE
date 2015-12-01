module Tree where
import PGF
import PGF.Internal
import Data.Maybe

type Path = [Int]
type UPath = [Pos]
type Pos = Int

data UTree =
  UEApp UTree UTree Pos
  | UEFun CId Pos

instance Show UTree where
  show (UEApp e1 e2 p) = "(App:" ++ show p ++ " " ++ show e1 ++ " " ++ show e2 ++ ")"
  show (UEFun cid p) = "(Fun:" ++ show p ++ " " ++ show cid ++ ")"
  
data GenericTree = Node String [GenericTree]

data UGenericTree = UNode Pos String [UGenericTree]


  
tree2utree :: Tree -> Int -> (Int,UTree)
tree2utree (EApp e1 e2) i =
  let (d1,ut1) = tree2utree e1 (i+1)
      (d2,ut2) = tree2utree e2 (d1+1)
  in (d2, UEApp ut1 ut2 i)
tree2utree (EFun id) i =
  (i,UEFun id i)

path2upath :: UTree -> Path -> Maybe UPath
path2upath ut [] = Just []
path2upath (UEFun id pos) [0] = Just [pos]
path2upath (UEApp e1 e2 pos) (p:rest)
  | p == 0 = let next = (path2upath e1 rest) in if isJust next then Just (pos:(fromJust next)) else Nothing
  | p == 1 = let next = (path2upath e2 rest) in if isJust next then Just (pos:(fromJust next)) else Nothing
  | otherwise = Nothing

-- My version of showBracketedString with slightly different output and primarily used to understand the BracketedString data type
showTree :: BracketedString -> String
showTree (Leaf token) = "\"" ++ token ++ "\""
showTree (Bracket cat fid lindex fun exps bss) =
  "(" ++ showCId fun ++ ":" ++ showCId cat ++ " " ++ (unwords $ map showTree bss) ++ ")"

-- Select a node in a BracketedString determined by a path
selectNode :: BracketedString -> [Int] -> Maybe BracketedString
selectNode t [] = Just t
selectNode t (pos:rest) =
  let branch = (selectBranch t pos) in
  case branch of {
    Just b ->  selectNode b rest ;
    Nothing -> Nothing
    }

-- Given a BracketedString, select one of the possible branches determined by an integer
selectBranch :: BracketedString -> Int -> Maybe BracketedString
selectBranch (Leaf token) i
  | i == 0 = Just (Leaf token)
  | otherwise = Nothing
selectBranch (Bracket cat fid lindex fun exps bss) i
  | i >= length bss = Nothing
  | otherwise = Just (bss !! i)
