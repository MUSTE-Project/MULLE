{-# language OverloadedStrings #-}
-- |
-- High level api to the muste backend
module Muste
  ( -- * Trees
    module Muste.Tree
  -- * Grammar
  , module Muste.Grammar
  -- * Menus
  , CostTree
  , getCleanMenu
  -- * Linearization
  , module Muste.Linearization
  ) where

import Data.List
import qualified Data.Map.Lazy as M
import Data.Aeson

import Muste.Tree
import Muste.Grammar
import qualified Muste.Prune as Prune
import Muste.Linearization
import Muste.Linearization.Internal (Linearization, mkLinearization)

-- FIXME Change the projection `_tree` to be a `TTree`
data CostTree = CostTree
  { _cost :: Int
  , _lin :: [Linearization]
  , _tree :: TTree
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

-- | @'getPrunedSuggestions' ctxt tree@ finds all trees similar to
-- @tree@ in @ctxt@.  Return a mapping from 'Path''s to the
-- @CostTree@'s you get when you replace one of the valid trees into
-- that given position along with the "cost" of doing so.
--
-- These cost trees are supposed to be grouped somehow, I don't quite
-- remember what the idea with this is, but currently the outermost
-- list is always a singleton.
getPrunedSuggestions :: Context -> TTree -> [(Path, [[CostTree]])]
getPrunedSuggestions ctxt tree = do
  (path, ts) <- Prune.replaceTrees (ctxtGrammar ctxt) (ctxtPrecomputed ctxt) tree
  -- pure $ (path, costTrees path trees)
  pure $ (path, costTrees path ts)
    where
    costTrees :: Path -> [(Int, TTree)] -> [[CostTree]]
    costTrees path trees = pure $ uncurry (costTree ctxt) <$> trees

-- | Creates a 'CostTree' from a tree and it's cost.  Since the cost
-- is already calculated, it basically just linearizes the tree.
costTree :: Context -> Int -> TTree -> CostTree
costTree ctxt cost fullTree = CostTree cost lin fullTree
  where
  lin = mkLinearization <$> linearizeTree ctxt fullTree

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
