{-# language OverloadedStrings #-}
{- |
  High level api to the muste backend
-}
module Muste
  -- Maybe put this in a seperate module.
  ( Context
  , CostTree(CostTree)
  , buildContext
  -- * Menus
  , getCleanMenu
  ) where

import Data.List
import qualified Data.Map.Lazy as M
import Data.Aeson

import Muste.Tree
import Muste.Grammar
import Muste.Grammar.Internal (ttreeToGFAbsTree)
import Muste.Prune
import Muste.Linearization

-- FIXME Change the projection `_tree` to be a `TTree`
data CostTree = CostTree
  { _cost :: Int
  , _lin :: [Linearization]
  , _tree :: String
  } deriving (Show,Eq)

instance FromJSON CostTree where
  parseJSON = withObject "CostTree" $ \v -> CostTree
    <$> v .: "cost"
    <*> v .: "lin"
    <*> v .: "tree"

instance ToJSON CostTree where
    toJSON (CostTree score lin tree) = object
      [ "score" .= score
      , "lin"   .= lin
      , "tree"  .= tree
      ]

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

{-# deprecated showTTree "use @show@" #-}
showTTree :: TTree -> String
showTTree = show
