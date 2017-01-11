{- |
  High level api to the muste backend
-}
module Muste where
import qualified Data.Set as S
import Muste.Tree
import Muste.Grammar
import PGF
import PGF.Internal (Expr(..))
import Debug.Trace
import Data.Maybe
import Data.List
import Test.QuickCheck hiding (generate)
import qualified Test.QuickCheck as Q

type LinToken = (Path,String)

-- | Type for a click that has both a position and a count
data Click = Click { pos :: Int, count :: Int } deriving (Show)

-- | Click is in the Arbitrary class for QuickCheck
instance Arbitrary Click where
  arbitrary =
    do
      pos <- arbitrary
      count <- arbitrary
      return $ Click pos count
      
updateClick :: Maybe Click -> Pos -> Maybe Click
updateClick Nothing pos = Just $ Click pos 1
updateClick (Just (Click pos count)) newPos
  | pos == newPos = Just $ Click pos (count + 1)
  | otherwise = Just $ Click newPos 1
  
-- | The 'linearizeTree' function linearizes a MetaTTree to a list of tokens and pathes to the nodes that create it
linearizeTree :: Grammar -> Language -> MetaTTree ->  [LinToken]
linearizeTree grammar lang tree = 
  let
    -- Convert the BracketedString to the list of string/path tuples
    bracketsToTuples :: LTree -> BracketedString -> [LinToken]
    bracketsToTuples tree bs =
      let
        deep :: LTree -> BracketedString -> [LinToken]
        deep _     (Bracket _ _   _ _ _ []) = []
        -- Ordinary leaf
        deep ltree (Bracket _ fid _ _ _ [Leaf token]) =
          [(getPath ltree fid, token)]
        -- Meta leaf
        deep ltree (Bracket _ fid _ _ [n@(EMeta id)] _) =
          [(getPath ltree fid, "?" ++ show id)]
        -- In the middle of the tree
        deep ltree (Bracket _ fid _ _ _ bs) =
          broad ltree fid bs []
        broad :: LTree -> Int -> [BracketedString] -> [LinToken] -> [LinToken]
        -- End of node siblings
        broad _     _   []                 ts = ts
        -- Syncategorial word
        broad ltree fid (Leaf token:bss) ts =
          let
            b = broad ltree fid bss ts
          in
            (getPath ltree fid, token):b
        -- In the middle of the nodes
        broad ltree fid (bs:bss)           ts =
          let
            d = deep ltree bs
            b = broad ltree fid bss ts
          in
            d ++ b
      in
        deep tree bs

    ttree = metaTree tree
    ltree = ttreeToLTree ttree
    abstree = ttreeToGFAbsTree ttree
    pgfGrammar = pgf grammar
    abstree2 = head $ parse pgfGrammar (mkCId "ABC1") (fromJust $ readType "S") "a a a"
    brackets = bracketedLinearize pgfGrammar lang abstree :: [BracketedString]
  in
    if not $ null brackets then bracketsToTuples ltree $ head brackets else [([],"?0")]
    
-- | The 'linearizeList' functions concatenates a token list to a string, can contain the pathes for debugging and the positions
linearizeList :: Bool -> Bool -> [LinToken] -> String
linearizeList debug positions list =
  let
    conditionalString :: Bool -> String -> String
    conditionalString True s = s
    conditionalString False _ = ""
    extendedList = zip [0..] $ concatMap (\e@(ep,es) -> [(ep," "),e]) list ++ [([]," ")]
  in
    --  if debug then unwords $ map (\(pos,(path,s)) -> "(" ++ show pos ++ ") " ++ s ++ " " ++ show path) extendedList
    --else unwords $ map (\(pos,(_,s)) -> "(" ++ show pos ++ ") " ++ s) extendedList
    unwords $ map (\(pos,(path,s)) -> conditionalString positions ("(" ++ show pos ++ ") ") ++ s ++ conditionalString debug (" " ++ show path)) extendedList

-- | The 'getNewTrees' function generates a set of related subtrees given a MetaTTree and a path
getNewTrees :: Grammar -> Language -> MetaTTree -> Path -> Int -> S.Set MetaTTree
getNewTrees grammar lang tree path depth =
  let
    subTree :: TTree
    subTree = fromJust $ selectNode (metaTree tree) path
    -- Get category at path
    cat :: CId
    cat = getTreeCat subTree
    -- Generate Trees with same category
    newSubTrees :: S.Set MetaTTree
    newSubTrees = generate grammar cat depth
  in
    newSubTrees
    
-- | The 'treesToStrings' generates a list of strings based on the differences in similar trees
treesToStrings :: Grammar -> Language -> [MetaTTree] -> [String]
treesToStrings grammar lang trees =
  map (linearizeList False False . linearizeTree grammar lang) trees

-- Comput sum of the length of the longest common suffix and suffix for linearized trees
preAndSuffix :: Eq a => [a] -> [a] -> (Int,Int)
preAndSuffix [] _  = (0,0)
preAndSuffix _  [] = (0,0)
preAndSuffix a b =
--  if a == b then 1 + preAndSuffix resta restb else preAndSuffix (reverse resta) (reverse restb)
  let prefix :: Eq a => [a] -> [a] -> Int -> Int ->(Int,Int)
      prefix [] _ pre suf = (pre,suf)
      prefix _ [] pre suf = (pre,suf)
      prefix (a:resta) (b:restb) pre suf
        | a == b = prefix resta restb (pre + 1) suf
        | otherwise = prefix resta restb pre (postfix (reverse (a:resta)) (reverse (b:restb)) 0)
      postfix :: Eq a => [a] -> [a] -> Int -> Int
      postfix [] _ suf = suf
      postfix _ [] suf = suf
      postfix (a:resta) (b:restb) suf
        | a == b = postfix resta restb (suf + 1)
        | otherwise = suf
  in
    prefix a b 0 0
    
createSortedTreeList :: Grammar -> Language ->MetaTTree -> S.Set MetaTTree -> [MetaTTree]
createSortedTreeList grammar language tree trees =
  let
     treeList :: [MetaTTree]
     treeList = S.toList trees
     referenceLin :: [String]
     referenceLin = map snd $ linearizeTree grammar language tree
     costList :: [Int]
     costList = map (\t -> uncurry (+) $ preAndSuffix referenceLin (map snd $ linearizeTree grammar language t)) treeList
  in
    sortBy (\a b -> compare (length $ linearizeTree grammar language a) (length $ linearizeTree grammar language b)) $ map snd $ sortBy (\(a,_) (b,_) -> compare b a ) $ zip costList treeList
    
                                                        
  -- | The 'getSuggestions' function generates a list of similar subtrees given a tree and a position in the token list ordered by some measure
getSuggestions :: Grammar -> Language -> MetaTTree -> Path -> Bool -> Int -> [(String, MetaTTree)]
getSuggestions grammar language tree path extend depth =
  let
    extension = if extend then 1 else 0
    subTree = flip MetaTTree S.empty $ fromJust $ selectNode (metaTree tree) path
    nTrees = filter (\t -> ((length $ linearizeTree grammar language subTree) + extension) == (length $ linearizeTree grammar language t)) $ createSortedTreeList grammar language subTree $ S.filter (not . hasMetas . metaTree ) $ getNewTrees grammar language tree path depth
    suggestions = treesToStrings grammar language nTrees
  in
    -- trace (show $ length nTrees) $ []
    zip suggestions nTrees

