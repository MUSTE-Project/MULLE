-- module Muste where
import PGF
--import PGF.Internal
import Data.Maybe

type Path = [Int]
type Weight = Int

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

-- precompute :: PGF -> Tree -> Path -> [(Path, Tree,Weight)]
-- precompute pgf tree [] = []
-- precompute pgf tree path =
--   let b = selectBranch tree (head path)
--   in
--     precompute pgf b (tail path)

-- Find a subtree in a BracketedString and return the path to it
findPath :: BracketedString -> BracketedString -> Maybe [Int]
findPath tree needle =
   let (Bracket cat1 _ _ fun1 _ bss1) = tree
       (Bracket cat2 _ _ fun2 _ bss2) = needle
   in
   if cat1 == cat2 && fun1 == fun2 && map showBracketedString bss1 == map showBracketedString bss2 then Just []
   else
     Nothing --map (\b -> findPath b needle) bss1
     
       
main =
  do
    grammar <- readPGF "gf/ABCAbs.pgf"
    let lang = (head $ languages grammar)
    let scat = (startCat grammar)
--    let parsesB = parse_ grammar lang scat (Just 4) "a b c d e" -- "the wolf drinks the milk"
    let parses1 = parse grammar lang scat "b d e f" -- "the wolf drinks the milk"
    let parses2 = parse grammar lang scat "d e a b c"
--    putStrLn $ showBracketedString (snd parsesB) -- map (\x -> showExpr [] x) parses
    putStrLn $ showBracketedString $ head $ bracketedLinearize grammar lang (head parses1)
    putStrLn $ showBracketedString $ head $ bracketedLinearize grammar lang (head parses2)
--    putStrLn $ show (mkApp (mkCId "bla") [(mkApp (mkCId "apply") [])])
    putStrLn $ unwords $ map showTree $ concat (map (\p -> bracketedLinearize grammar lang p) parses1)
    let node = selectNode (head $ bracketedLinearize grammar lang (head parses1)) [0,0,1,1,0]
    putStrLn $ showBracketedString $ fromJust $ node -- map (\x -> showExpr [] x) parses
--    findPath (head $ bracketedLinearize grammar lang (head parses1)) node
