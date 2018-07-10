{- |
  High level api to the muste backend
-}
module Muste
  ( LinToken(LinToken, ltlin, ltpath) -- NB ltlin and ltpath should not be exposed
  , Context
  , CostTree(CostTree)
  , buildContext
  -- ^ Menus
  , getCleanMenu
  -- ^ Linearizations
  , Linearization(Linearization, lpath, llin) -- NB lpath and llin should not be exposed
  , linearizeTree
  ) where

import Muste.Tree
import Muste.Grammar
import PGF
import PGF.Internal (Expr(..))
import qualified Data.Map.Lazy as M

import Muste.Prune
import Data.List

type PrecomputedTrees = AdjunctionTrees
type Context = (Grammar, Language, PrecomputedTrees)


data LinToken = LinToken { ltpath :: Path, ltlin :: String, _ltmatched :: Path } deriving (Show)
data Linearization = Linearization { lpath :: Path, llin :: String } deriving (Show,Eq)
data CostTree = CostTree { _cost :: Int , _lin :: [Linearization] , _tree :: String } deriving (Show,Eq)


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
        deep ltree (Bracket _ fid _ _ [EMeta id] _) =
          [(LinToken (getPath ltree fid) ("?" ++ show id) [])]
        -- In the middle of the tree
        deep ltree (Bracket _ fid _ _ _ bs) =
          broad ltree fid bs []
        deep _ _ = error "Muste.linearizeTree: Non-exhaustive pattern match"
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
    filtered2 = [r | r@(_p,tss) <- filtered1, tss /= [] && tss /= [[]]]
    -- sort by cost
    compareCostTrees (CostTree c1 _ _) (CostTree c2 _ _) = compare c1 c2
    sorted = [(p, [sortBy compareCostTrees ts | ts <- tss]) | (p, tss) <- filtered2]
  in
    sorted

getCleanMenu :: Context -> TTree -> M.Map Path [[CostTree]]
getCleanMenu context tree = M.fromList $ filterCostTrees $ getPrunedSuggestions context tree
