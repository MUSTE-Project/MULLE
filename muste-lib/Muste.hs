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


type PrecomputedTrees = AdjunctionTrees
type Context = (Grammar, Language, PrecomputedTrees)


data LinToken = LinToken { ltpath :: Path, ltlin :: String, ltmatched :: Path } deriving (Show)
data Linearization = Linearization { lpath :: Path, llin :: String } deriving (Show,Eq)
data CostTree = CostTree { cost :: Int , lin :: [Linearization] , tree :: String } deriving (Show,Eq)


buildContext :: Grammar -> CId -> Context
buildContext grammar lang = (grammar, lang, getAdjunctionTrees grammar)


-- lin is the full linearization
-- | The 'linearizeTree' function linearizes a TTree to a list of tokens and pathes to the nodes that create it
linearizeTree :: Context -> TTree ->  [LinToken]
linearizeTree (grammar, language, _) ttree = 
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


rateTree :: Context -> TTree -> TTree -> Int
rateTree context t1 t2 =
  let
    lin1 = [w | LinToken _ w _ <- linearizeTree context t1]
    lin2 = [w | LinToken _ w _ <- linearizeTree context t2]
    (p,s) = preAndSuffix lin1 lin2
    nct1 = countNodes t1
    nmch1 = countMatchedNodes t1 t2
    nct2 = countNodes t2
    nmch2 = countMatchedNodes t2 t1
  in
    length lin2 - (length p) - (length s) + (nct2 - nmch1)

getPrunedSuggestions :: Context -> TTree -> [(Path, [[CostTree]])]
getPrunedSuggestions context@(grammar, _, precomputed) tree =
    [ (path, [[ CostTree cost lin (showTTree fullTree) |
                (cost, subtree, _, _) <- trees,
                let fullTree = replaceNode tree path subtree,
                let lin = [Linearization p l | (LinToken p l _) <- linearizeTree context fullTree]
              ]]) |
      (path, _, trees) <- collectSimilarTrees grammar precomputed tree
    ]

filterCostTrees :: [(Path, [[CostTree]])] -> [(Path, [[CostTree]])]
filterCostTrees trees =
  let
    filtered1, filtered2 :: [(Path, [[CostTree]])]
    -- remove trees of cost 0
    filtered1 = [(p, [[t | t@(CostTree c _ _) <- ts, c /= 0] | ts <- tss]) | (p, tss) <- trees]
    -- remove empty menus
    filtered2 = [r | r@(p,tss) <- filtered1, tss /= [] && tss /= [[]]]
    -- sort by cost
    compareCostTrees (CostTree c1 _ _) (CostTree c2 _ _) = compare c1 c2
    sorted = [(p, [sortBy compareCostTrees ts | ts <- tss]) | (p, tss) <- filtered2]
  in
    sorted

-- | Removes menu items further up in the tree if they already show up further down
-- | Attention: Assumes that [[CostTree] actually contains only one menu
thoroughlyClean :: [(Path,[[CostTree]])] -> [(Path,[[CostTree]])]
thoroughlyClean [] = []
thoroughlyClean ((p,[ts]):pts) = (p, [ts]) : thoroughlyClean [(pp, [tt \\ ts]) | (pp, [tt]) <- pts]

getCleanMenu :: Context -> TTree -> M.Map Path [[CostTree]]
getCleanMenu context tree = M.fromList $ filterCostTrees $ getPrunedSuggestions context tree

showCleanMenu :: Context -> M.Map Path [[CostTree]] -> String
showCleanMenu context menu =
    unlines [show path ++ " :\n" ++ unlines [showCostTree context path t | ts <- trees, t <- ts] |
             path <- sort (M.keys menu), let trees = menu M.! path]

showCostTree :: Context -> Path -> CostTree -> String
showCostTree (grammar, _, _) path (CostTree cost lin tree) =
    ("\t" ++ show cost ++ " - " ++
     unwords [w | Linearization _ w <- lin] ++ " - " ++
     (showTTree $ fromJust $ selectNode (gfAbsTreeToTTree grammar (read tree)) path))

