{- |
  High level api to the muste backend
-}
module Muste where

import Muste.Tree
import Muste.Grammar
import PGF
import PGF.Internal (Expr(..))
import Data.Maybe
import qualified Data.Map.Lazy as M

import Muste.Prune


import Data.List

type Context = (Grammar,Language)

-- type LinToken = (Path,String)
  

data LinToken = LinToken { ltpath :: Path, ltlin :: String, ltmatched :: Path } deriving (Show)
data Linearization = Linearization { lpath :: Path, llin :: String } deriving (Show,Eq)
data CostTree = CostTree { cost :: Int , lin :: [Linearization] , tree :: String } deriving (Show,Eq)

-- lin is the full linearization
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
          [(LinToken (getPath ltree fid) token [])]
        -- Meta leaf
        deep ltree (Bracket _ fid _ _ [n@(EMeta id)] _) =
          [(LinToken (getPath ltree fid) ("?" ++ show id) [])]
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
            (LinToken (getPath ltree fid) token []):b
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
    if (not $ isEmptyGrammar grammar) && elem language (languages $ pgf grammar) && (not $ null brackets) then bracketsToTuples ltree $ head brackets else [(LinToken [] "?0" [])]

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
    
type PrecomputedTrees = [((TTree,Path),[(Int,[(Path,String)],TTree)])]

-- Language -> PrecomputedTrees
type Precomputed = M.Map Language PrecomputedTrees

-- Lesson -> Precomputed
type LessonsPrecomputed = M.Map String Precomputed

precomputeTrees :: Context -> TTree -> PrecomputedTrees
precomputeTrees context@(grammar,_) tree =
  let
    cat = getTreeCat tree
    lin = linearizeTree context tree
--    allTrees = generateTrees grammar cat (maxDepth tree + 5) -- Problem?!?
    allTrees = concat $ take (countNodes tree + 1) $ generateTrees grammar cat 
  in
    [((t,p),getScoredTrees context t p) | t <- allTrees, p <- getPathes t]

rateTree :: Context -> TTree -> TTree -> Int
rateTree context t1 t2 =
  let
    lin1 = (map ltlin $ linearizeTree context t1)
    lin2 = (map ltlin $ linearizeTree context t2)
    (p,s) = preAndSuffix lin1 lin2
    nct1 = countNodes t1
    nmch1 = countMatchedNodes t1 t2
    nct2 = countNodes t2
    nmch2 = countMatchedNodes t2 t1
  in
    length lin2 - (length p) - (length s) + (nct2 - nmch1)

newTrees :: Context -> TTree -> Path -> [TTree]
newTrees context t path =
  let
    subTree = fromJust $ selectNode t path
    cat = getTreeCat subTree
    -- Should be fixed but leads to performance problems
--    suggestions = filter (\n -> maxDepth n <= maxDepth subTree + 2) $ generateTrees (fst context) cat (maxDepth subTree + 2)
    -- suggestions = filter (\n -> maxDepth n <= maxDepth subTree + 1) $ concat $ drop (countNodes subTree `div` 2 - 1) $ generateTrees (fst context) cat (countNodes subTree)
    suggestions = filter (\n -> maxDepth n <= maxDepth subTree + 1) $ concat $ take (countNodes subTree + 1) (generateTrees (fst context) cat)
  in
    map (replaceNode t path) suggestions

getScoredTrees :: Context -> TTree -> Path -> [(Int,[(Path,String)],TTree)]
getScoredTrees context t p =
  let
    nts = newTrees context t p
    scores = map (rateTree context t) nts :: [Int]
    lins = map (map (\(LinToken p l _) -> (p,l))) $ map (linearizeTree context) nts :: [[(Path,String)]]
  in
    zip3 scores lins nts
    
suggestionFromPrecomputed :: PrecomputedTrees -> TTree -> [(Path,[(Int,[(Path,String)],TTree)])]
suggestionFromPrecomputed [] _ = []
suggestionFromPrecomputed pc key =
   map (\((_,p),ts) -> (p,ts)) $ filter (\((t,_),_) -> t == key) pc

getSuggestions :: Context -> TTree -> [(Path,[(Int,[(Path,String)],TTree)])]
getSuggestions context tree =
  [ (p,getScoredTrees context tree p) | p <- getPathes tree]
  
getPrunedSuggestions :: Context -> TTree -> [(Path,[(Int,[(Path,String)],TTree)])]
getPrunedSuggestions context@(grammar,_) tree =
  let
    similar = collectSimilarTrees grammar (2,2) tree :: [(Path, TTree, [(Int, TTree, TTree, TTree)])]
  in
    map (\(path,_,trees) -> (path,map (\(cost, subtree,_,_) -> let fullTree = replaceNode tree path subtree in (cost, map (\(LinToken p l _) -> (p,l)) $ linearizeTree context fullTree, fullTree)) trees)) similar

-- | Convert between the muste suggestion output and the ajax cost trees
suggestionToCostTree :: (Path, [(Int,[(Path,String)],TTree)]) -> (Path,[[CostTree]])
suggestionToCostTree (path,trees) =
  (path, [map (\(cost,lin,tree) -> CostTree cost (map (uncurry Linearization) lin) (showTTree tree)) trees])

filterCostTrees :: [(Path,[[CostTree]])] -> [(Path,[[CostTree]])]
filterCostTrees trees =
  let
    -- remove trees of cost 1
    filtered1 = map (\(p,ts) -> (p,map (filter (\(CostTree c _ _) -> c /= 0)) ts)) trees :: [(Path,[[CostTree]])]
    -- remove menu items that already appear further down the tree
    filtered2 = thoroughlyClean $ sortBy (\(a,_) (b,_) -> compare (length b) (length a)) filtered1
    -- remove empty menus
    filtered3 = filter (\(p,ts) -> ts /= [] && ts /= [[]] ) filtered2 :: [(Path,[[CostTree]])]
    -- sort by cost
    sorted = map (\(p,ts) -> (p, map (sortBy (\(CostTree c1 _ _) (CostTree c2 _ _) -> compare c1 c2)) ts)) filtered3
  in
    sorted

-- | Removes menu items further up in the tree if they already show up further down
-- | Attention: Assumes that [[CostTree] actually contains only one menu
thoroughlyClean :: [(Path,[[CostTree]])] -> [(Path,[[CostTree]])]
thoroughlyClean [] = []
thoroughlyClean ((p,[ts]):pts) =
  (p,[ts]):(thoroughlyClean $ map (\(pp,[tt]) -> (pp,[tt \\ ts])) pts)

getCleanMenu :: Context -> TTree -> M.Map Path [[CostTree]]
getCleanMenu context tree =
  M.fromList $ filterCostTrees $ (map suggestionToCostTree) $ getPrunedSuggestions context tree

