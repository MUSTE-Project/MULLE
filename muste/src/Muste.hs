{-# Language
    OverloadedStrings
  , StandaloneDeriving
  , GeneralizedNewtypeDeriving
#-}
-- |
-- High level api to the muste backend
module Muste
  ( -- * Trees
    module Muste.Tree
  -- * Grammar
  , module Muste.Grammar
  -- * Menus
  , Menu
  , getCleanMenu
  , CostTree
  -- * Linearization
  , module Muste.Linearization
  ) where

import Data.List
-- FIXME I think we might need to consider switching to strict maps.
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Aeson
import Data.Text (Text(..),pack)

import Muste.Tree
import Muste.Grammar
import qualified Muste.Prune as Prune
import Muste.Linearization
import qualified Muste.Linearization.Internal as Linearization
  ( Linearization
  , linearizeTree
  )

-- FIXME Change the projection `_tree` to be a `TTree`
data CostTree = CostTree
  { _cost :: Int
  , _lin :: [Linearization.Linearization]
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
getPrunedSuggestions :: Context -> TTree -> Map Path [[CostTree]]
getPrunedSuggestions ctxt tree = go `Map.mapWithKey` Prune.replaceTrees (ctxtGrammar ctxt) (ctxtPrecomputed ctxt) tree
  where
  go :: Path -> [(Int, TTree)] -> [[CostTree]]
  go path ts = costTrees path ts
  costTrees :: Path -> [(Int, TTree)] -> [[CostTree]]
  costTrees path trees = pure $ uncurry (costTree ctxt) <$> trees

-- | Creates a 'CostTree' from a tree and it's cost.  Since the cost
-- is already calculated, it basically just linearizes the tree.
costTree :: Context -> Int -> TTree -> CostTree
costTree ctxt cost fullTree
  = CostTree cost (Linearization.linearizeTree ctxt fullTree) fullTree

filterCostTrees :: Map Path [[CostTree]] -> Menu
filterCostTrees trees =
  let
    filtered1, filtered2 :: Map Path [[CostTree]]
    -- remove trees of cost 0
    filtered1 = (\tss -> [[t | t@(CostTree c _ _) <- ts, c /= 0] | ts <- tss]) <$> trees
    -- remove empty menus
    filtered2 = Map.filter (\tss -> not (null tss) && not (null (head tss))) filtered1
    -- sort by cost
    compareCostTrees (CostTree c1 _ _) (CostTree c2 _ _) = compare c1 c2
  in
    Menu $ (\tss -> sortBy compareCostTrees <$> tss) <$> filtered2

getCleanMenu :: Context -> TTree -> Menu
getCleanMenu context tree
  = filterCostTrees
  $ getPrunedSuggestions context tree

newtype Menu = Menu (Map Path [[CostTree]]) deriving (Show)

instance FromJSON Menu where
  parseJSON = withObject "CostTree" $ \v -> Menu
    <$> v .: "menu"

instance ToJSON Menu where
    toJSON (Menu map) =
      object [ (pack $ show k) .= (Map.!) map  k | k <- Map.keys map]

deriving instance Semigroup Menu

deriving instance Monoid Menu
