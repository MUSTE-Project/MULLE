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
import Data.Monoid
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
  
-- | The 'linearizeTree' function linearizes a TTree to a list of tokens and pathes to the nodes that create it
linearizeTree :: Grammar -> Language -> TTree ->  [LinToken]
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

    ttree = tree
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

-- | The 'getNewTrees' function generates a set of related subtrees given a TTree and a path
getNewTrees :: Grammar -> Language -> TTree -> Path -> Int -> S.Set TTree
getNewTrees grammar lang tree path depth =
  let
    subTree :: TTree
    subTree = fromJust $ selectNode tree path
    -- Get category at path
    cat :: CId
    cat = getTreeCat subTree
    -- Generate Trees with same category
    newSubTrees :: S.Set TTree
    newSubTrees = generate grammar cat depth
  in
    newSubTrees
    
-- | The 'treesToStrings' generates a list of strings based on the differences in similar trees
treesToStrings :: Grammar -> Language -> [TTree] -> [String]
treesToStrings grammar lang trees =
  map (linearizeList False False . linearizeTree grammar lang) trees

-- Computes the longest common prefix and suffix for linearized trees
preAndSuffix :: Eq a => [a] -> [a] -> ([a],[a])
preAndSuffix [] _  = ([],[])
preAndSuffix _  [] = ([],[])
preAndSuffix a b =
  let prefix :: Eq a => [a] -> [a] -> [a] -> [a] ->([a],[a])
      prefix [] _ pre suf = (pre,suf)
      prefix _ [] pre suf = (pre,suf)
      prefix (a:resta) (b:restb) pre suf
        | a == b = prefix resta restb (pre ++ [a]) suf
        | otherwise = prefix resta restb pre (postfix (reverse (a:resta)) (reverse (b:restb)) [])
      postfix :: Eq a => [a] -> [a] -> [a] -> [a]
      postfix [] _ suf = suf
      postfix _ [] suf = suf
      postfix (a:resta) (b:restb) suf
        | a == b = postfix resta restb (a:suf)
        | otherwise = suf
  in
    prefix a b [] []
    
createSortedTreeList :: Grammar -> Language -> TTree -> S.Set TTree -> [TTree]
createSortedTreeList grammar language tree trees =
  let
     treeList :: [TTree]
     treeList = S.toList trees
     referenceLin :: [String]
     referenceLin = map snd $ linearizeTree grammar language tree
     costList :: [Int]
     costList = map (\t -> uncurry (\f s -> length f + length s) $ preAndSuffix referenceLin (map snd $ linearizeTree grammar language t)) treeList
  in
    -- Sort first by common pre/suffix, then by length of the linearized tree and finally by the linearization itself
    map snd $ sortBy (\(a1,a2) (b1,b2) -> let la = linearizeTree grammar language a2 in let lb = linearizeTree grammar language b2 in compare b1 a1 <> compare (length la) (length lb) <> compare la lb) $ zip costList treeList
                                                        
  -- | The 'getSuggestions' function generates a list of similar subtrees given a tree and a position in the token list ordered by some measure
getSuggestions :: Grammar -> Language -> TTree -> Path -> Bool -> Int -> [(String, TTree)]
getSuggestions grammar language tree path extend depth =
  let
    extension = if extend then 1 else 0
    subTree = fromJust $ selectNode tree path
    linSubTree = map snd $ linearizeTree grammar language subTree
    nTrees = filter (\t -> ((length $ linearizeTree grammar language subTree) + extension) >= (length $ linearizeTree grammar language t)) $ createSortedTreeList grammar language subTree $ S.filter (not . hasMetas ) $ getNewTrees grammar language tree path depth
    suggestions = treesToStrings grammar language nTrees
  in
    -- Remove element if it is equal to the original tree or if it is bigger but has nothing in common (prefix and suffix empty)
    filter (\(a,_) -> let wa = words a in wa /= linSubTree && let (pre,suf) = preAndSuffix wa linSubTree in (length wa == length linSubTree || length wa > length linSubTree && length pre + length suf /= 0)) $ zip suggestions nTrees

type PrecomputedTrees = [String] -- TODO

precomputeTrees :: Grammar -> Language -> TTree -> PrecomputedTrees
precomputeTrees grammar language tree = [] -- TODO
suggestionFromPrecomputed :: PrecomputedTrees -> Click -> [(String,TTree)]
suggestionFromPrecomputed pre click = [] -- TODO
