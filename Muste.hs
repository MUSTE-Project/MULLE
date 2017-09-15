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
import qualified Data.Map.Lazy as M

type Context = (Grammar,Language)

type LinToken = (Path,String)

-- | Type for a click that has both a position and a count
data Click = Click { pos :: Int, count :: Int } deriving (Show,Eq)

-- | Click is in the Arbitrary class for QuickCheck
instance Arbitrary Click where
  arbitrary =
    do
      pos <- arbitrary
      count <- arbitrary
      return $ Click pos count
      
-- | The function 'updateClick' either increases the counter when the position is the same as the previous one or sets the new position and sets the counter to 1
updateClick :: Maybe Click -> Pos -> Maybe Click
updateClick Nothing pos = Just $ Click pos 1
updateClick (Just (Click pos count)) newPos
  | pos == newPos = Just $ Click pos (count + 1)
  | otherwise = Just $ Click newPos 1
  
-- | The 'linearizeTree' function linearizes a TTree to a list of tokens and pathes to the nodes that create it
linearizeTree :: Context -> TTree ->  [LinToken]
linearizeTree (grammar,language) ttree = 
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

    ltree = ttreeToLTree ttree
    abstree = ttreeToGFAbsTree ttree
    pgfGrammar = pgf grammar
    brackets = bracketedLinearize pgfGrammar language abstree :: [BracketedString]
  in
    if (not $ isEmptyGrammar grammar) && elem language (languages $ pgf grammar) && (not $ null brackets) then bracketsToTuples ltree $ head brackets else [([],"?0")]
    
-- | The 'linearizeList' functions concatenates a token list to a string, can contain the pathes for debugging and the positions
linearizeList :: Bool -> Bool -> [LinToken] -> String
linearizeList debug positions list =
  let
    conditionalString :: Bool -> String -> String
    conditionalString True s = s
    conditionalString False _ = ""
    extendedList :: [(Integer, (Path, [Char]))]
--    extendedList = zip [0..] $ concatMap (\e@(ep,es) -> [(ep," "),e]) list ++ [([]," ")] -- the end of the list is always pointing to the root of the tree
    extendedList = zip [0..] $ if debug || positions then concatMap (\e@(ep,es) -> [(ep," "),e]) list ++ [([]," ")] -- insert "gaps between the words and point the end of the list to the root of the tree
                               else list 
  in
    --  if debug then unwords $ map (\(pos,(path,s)) -> "(" ++ show pos ++ ") " ++ s ++ " " ++ show path) extendedList
    --else unwords $ map (\(pos,(_,s)) -> "(" ++ show pos ++ ") " ++ s) extendedList
    unwords $ map (\(pos,(path,s)) -> conditionalString positions ("(" ++ show pos ++ ") ") ++ s ++ conditionalString debug (" " ++ show path)) extendedList

-- | The 'getNewTrees' function generates a set of related subtrees given a TTree and a path
-- getNewTreesSet :: Context -> TTree -> Path -> Int -> S.Set TTree
-- getNewTreesSet (grammar,_) tree path depth =
--   let
--     subTree :: TTree
--     subTree = fromJust $ selectNode tree path
--     -- Get category at path
--     cat :: String
--     cat = getTreeCat subTree
--     -- Generate Trees with same category
--     newSubTrees :: S.Set TTree
--     newSubTrees = generateSet grammar cat depth
--   in
--     newSubTrees

-- | The 'getNewTrees' function generates a set of related subtrees given a TTree and a path
getNewTrees :: Context -> TTree -> Path -> Int -> [TTree]
getNewTrees (grammar,_) tree path depth =
  let
    subTree :: TTree
    subTree = fromJust $ selectNode tree path
    -- Get category at path
    cat :: String
    cat = getTreeCat subTree
    -- Generate Trees with same category
    newSubTrees :: [TTree]
    newSubTrees = generateList grammar cat depth -- Might be problematic
  in
    newSubTrees
    
-- | The 'treesToStrings' generates a list of strings based on the differences in similar trees
treesToStrings :: Context -> [TTree] -> [String]
treesToStrings context trees =
  map (linearizeList False False . linearizeTree context) trees

-- Computes the longest common prefix and suffix for linearized trees
preAndSuffix :: Eq a => [a] -> [a] -> ([a],[a])
preAndSuffix [] _  = ([],[])
preAndSuffix _  [] = ([],[])
preAndSuffix a b =
  let prefix :: Eq a => [a] -> [a] ->([a],[a])
      prefix [] _ = ([],[])
      prefix _ [] = ([],[])
      prefix (a:resta) (b:restb)
        | a == b = let (pre,suf) = prefix resta restb in (a:pre,suf)
        | otherwise = ([],reverse $ postfix (reverse (a:resta)) (reverse (b:restb)))
      postfix :: Eq a => [a] -> [a] -> [a]
      postfix [] _ = []
      postfix _ [] = []
      postfix (a:resta) (b:restb)
        | a == b = let suf = postfix resta restb in (a:suf)
        | otherwise = []
  in
    prefix a b
    
createSortedTreeList :: Context -> TTree -> S.Set TTree -> [TTree]
createSortedTreeList context tree trees =
  let
     treeList :: [TTree]
     treeList = S.toList trees
     referenceLin :: [String]
     referenceLin = map snd $ linearizeTree context tree
     costList :: [Int]
     costList = map (\t -> uncurry (\f s -> length f + length s) $ preAndSuffix referenceLin (map snd $ linearizeTree context t)) treeList
  in
    -- Sort first by common pre/suffix, then by length of the linearized tree and finally by the linearization itself
    map snd $ sortBy (\(a1,a2) (b1,b2) -> let la = linearizeTree context a2 in let lb = linearizeTree context b2 in compare b1 a1 <> compare (length la) (length lb) <> compare la lb) $ zip costList treeList

createSortedTreeListFromList :: Context -> TTree -> [TTree] -> [TTree]
createSortedTreeListFromList context tree treeList =
  let
     referenceLin :: [String]
     referenceLin = map snd $ linearizeTree context tree
     costList :: [Int]
     costList = map (\t -> uncurry (\f s -> length f + length s) $ preAndSuffix referenceLin (map snd $ linearizeTree context t)) treeList
  in
    -- Sort first by common pre/suffix, then by length of the linearized tree and finally by the linearization itself
    map snd $ sortBy (\(a1,a2) (b1,b2) -> let la = linearizeTree context a2 in let lb = linearizeTree context b2 in compare b1 a1 <> compare (length la) (length lb) <> compare la lb) $ zip costList treeList
                                                        
  -- | The 'getSuggestions' function generates a list of similar subtrees given a tree and a position in the token list ordered by some measure
getSuggestions :: Context -> TTree -> Path -> Bool -> Int -> [(String, TTree)]
getSuggestions context tree path extend depth =
  let
    extension = if extend then 1 else 0
    subTree = fromJust $ selectNode tree path
    --linSubTree = map snd $ linearizeTree grammar language subTree
    linTree = linearizeList False False $ linearizeTree context tree
    --newTrees = getNewTreesSet grammar language tree path depth
    newTrees = getNewTrees context tree path depth -- version working with lists
    --filteredNewTrees = S.filter (not . hasMetas ) $ newTrees
    filteredNewTrees = filter (not . hasMetas ) $ newTrees -- version working with lists
    --sortedNewTrees = createSortedTreeList grammar language subTree filteredNewTrees
    --sortedNewTrees = createSortedTreeListFromList grammar language subTree filteredNewTrees -- version working with lists
    --nTrees = filter (\t -> ((length $ linearizeTree grammar language subTree) + extension) >= (length $ linearizeTree grammar language t)) $ sortedNewTrees
    assembledTrees = map (replaceNode tree path) filteredNewTrees
    suggestions = treesToStrings context assembledTrees
  in
    -- Remove element if it is equal to the original tree or if it is bigger but has nothing in common (prefix and suffix empty)
    -- filter (\(a,_) ->
    --          let wa = words a in
    --          wa /= linSubTree
    --          &&
    --          let (pre,suf) = preAndSuffix wa linSubTree in
    --          (length wa <= length linSubTree || (length wa > length linSubTree && length pre + length suf /= 0))) $ zip suggestions nTrees
    --          -- length pre + length suf /= 0) $ zip suggestions nTrees -- bork, why?
    filter (\(s,_) -> s /= linTree && (length $ words s) == (extension + (length $ words linTree))) $ zip suggestions assembledTrees


type PrecomputedTrees = [((TTree,Click),[(Int,String,TTree)])] -- TODO

precomputeTrees :: Context -> TTree -> PrecomputedTrees
precomputeTrees context@(grammar,_) tree =
  let
    lin = linearizeTree context tree
    allTrees = map (gfAbsTreeToTTreeWithGrammar grammar) $ generateAllDepth (pgf grammar) (fromJust $ readType $ startcat grammar) (Just 5) -- depth might be problematic
    allClicks = [Click p c | p <- [0..length lin -1], c <- [0..length (fst (lin !! p)) -1]]
  in
    [((t,c),getScoredTrees context t c) | c <- allClicks, t <- allTrees] --, nt <- newTrees context t c]
--    [((t,c),[]) | c <- allClicks, t <- allTrees] --, nt <- newTrees context t c]

rateTree :: Context -> TTree -> TTree -> Int
rateTree context t1 t2 =
  let
    lin1 = (map snd $ linearizeTree context t1)
    lin2 = (map snd $ linearizeTree context t2)
    (p,s) = preAndSuffix lin1 lin2
  in
    length lin1 - (length p) - (length s)

newTrees :: Context -> TTree -> Click -> [TTree]
newTrees context t c =
  let
    lin = linearizeTree context t
    path = initN (count c) $ fst (lin !! (pos c))
    -- suggestions = getSuggestions context t path True 4
    subTree = fromJust $ selectNode t path
    cat = getTreeCat $ subTree
    suggestions = filter (\n -> maxDepth n <= maxDepth subTree + 1) $ generateList (fst context) cat (maxDepth subTree + 1)
  in
    -- map snd suggestions
    suggestions

initN :: Int -> [a] -> [a]
initN ct l =
  take (length l - ct) l
  
linearizeSubtree :: Context -> TTree -> Click -> String
linearizeSubtree context t c =
  let
    lin = linearizeTree context t
    path = initN (count c) $ fst (lin !! (pos c))
  in
    concat $ map snd $ linearizeTree context $ fromJust $ selectNode t path -- Might explode if path is invalid 

-- This function makes probably too simple assumptions
-- 1. the range starts at click position
-- 2. the range is as long as the linearization of the subtree
clickToRange :: Context -> TTree -> Click -> (Int,Int)
clickToRange context tree (Click pos count) =
  let
    linTree = linearizeTree context tree
    path = initN count $ fst (linTree !! pos)
    -- lin = linearizeTree context (fromJust $ selectNode tree path)
  in
    -- (pos,pos + length lin)
    (pos, pos + (length $ filter (isPrefixOf path) $ map fst linTree))
    
getScoredTrees :: Context -> TTree -> Click -> [(Int,String,TTree)]
getScoredTrees context t c =
  let
    nts = newTrees context t c
    scores = map (rateTree context t) nts
    lins = map ((flip $ linearizeSubtree context) c) nts
  in
    zip3 scores lins nts
    
suggestionFromPrecomputed :: Context -> PrecomputedTrees -> TTree -> [((Int,Int),[(Int,String,TTree)])]
suggestionFromPrecomputed _ [] _ = []
suggestionFromPrecomputed context pc key =
  map (\((_,c),ts) -> let range = clickToRange context key c in (range,ts)) $ filter (\((t,_),_) -> t == key) pc
--  if (fst $ fst p) == key then (range,(snd p)):(suggestionFromPrecomputed context pre key)
--  else suggestionFromPrecomputed context pre key
--  where range = clickToRange context key (snd $ fst p)
