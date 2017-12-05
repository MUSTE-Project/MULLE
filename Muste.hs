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

type Context = (Grammar,Language)

type LinToken = (Path,String)
  
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

type Precomputed = M.Map Language PrecomputedTrees

type LessonsPrecomputed = M.Map String Precomputed

precomputeTrees :: Context -> TTree -> PrecomputedTrees
precomputeTrees context@(grammar,_) tree =
  let
    cat = getTreeCat tree
    lin = linearizeTree context tree
    allTrees = generateTrees grammar cat (maxDepth tree + 2)
  in
    [((t,p),getScoredTrees context t p) | t <- allTrees, p <- getPathes t]

rateTree :: Context -> TTree -> TTree -> Int
rateTree context t1 t2 =
  let
    lin1 = (map snd $ linearizeTree context t1)
    lin2 = (map snd $ linearizeTree context t2)
    (p,s) = preAndSuffix lin1 lin2
  in
    length lin1 - (length p) - (length s)

newTrees :: Context -> TTree -> Path -> [TTree]
newTrees context t path =
  let
    subTree = fromJust $ selectNode t path
    cat = getTreeCat subTree
    suggestions = filter (\n -> maxDepth n <= maxDepth subTree + 2) $ generateTrees (fst context) cat (maxDepth subTree + 2)
  in
    map (replaceNode t path) suggestions

getScoredTrees :: Context -> TTree -> Path -> [(Int,[(Path,String)],TTree)]
getScoredTrees context t p =
  let
    nts = newTrees context t p
    scores = map (rateTree context t) nts
    lins = map (linearizeTree context) nts
  in
    zip3 scores lins nts
    
suggestionFromPrecomputed :: Context -> PrecomputedTrees -> TTree -> [(Path,[(Int,[(Path,String)],TTree)])]
suggestionFromPrecomputed _ [] _ = []
suggestionFromPrecomputed context pc key =
  map (\((_,p),ts) -> (p,ts)) $ filter (\((t,_),_) -> t == key) pc
