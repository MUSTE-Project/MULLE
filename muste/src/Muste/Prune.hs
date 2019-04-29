{-# OPTIONS_GHC -Wall -Wno-unused-top-binds -Wno-name-shadowing #-}
{-# Language
 ConstraintKinds,
 DerivingStrategies,
 OverloadedStrings,
 ScopedTypeVariables,
 StandaloneDeriving
#-}

module Muste.Prune
  ( replaceAllTrees
  , PruneOpts(..)
  , emptyPruneOpts
  ) where

import Control.Monad (guard)

import qualified Data.Containers as Mono
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.MultiSet as MultiSet

import Muste.Tree (TTree(..), Path, FunType(..), Category)
import qualified Muste.Tree as Tree
import qualified Muste.Grammar as Grammar
import Muste.AdjunctionTrees hiding (BuilderInfo(..))


-- * Replacing trees

replaceAllTrees :: PruneOpts -> AdjunctionTrees -> [TTree] -> [(TTree, TTree)]
replaceAllTrees opts adjTrees base_trees
    = do (adjtree :: AdjTree, branches_and_parents) <- Map.toList pruned_map
         simtree :: TTree <- Map.findWithDefault [] adjtree new_sims_map
         (branches :: [TTree], parents :: Set (TTree, Path)) <- Map.toList branches_and_parents
         subtree :: TTree <- insertBranches branches simtree
         (oldtree :: TTree, path :: Path) <- Set.toList parents
         let newtree :: TTree = Tree.replaceNode oldtree path subtree
         return (oldtree, newtree)

    where
      pruned_map :: Map AdjTree (Map [TTree] (Set (TTree, Path)))
      pruned_map = splitAndPruneTrees opts base_trees

      sims_map :: Map AdjTree [TTree]
      sims_map = Map.mapWithKey getSims pruned_map
          where getSims adjtree _ = getSimTrees adjTrees adjtree

      new_sims_map :: Map AdjTree [TTree]
      new_sims_map = Map.fromList $
          do (adjtree :: AdjTree, simtrees :: [TTree]) <- Map.toList sims_map
             let simtrees' :: Set TTree = Set.fromList simtrees
             let toremove :: Set TTree = simtrees_to_remove adjtree simtrees'
             let new_simtrees = simtrees' `Set.difference` toremove
             return (adjtree, Set.toList new_simtrees)

      simtrees_to_remove :: AdjTree -> Set TTree -> Set TTree
      simtrees_to_remove adjtree simtrees = Set.fromList $
          do (upper_tree :: AdjTree, lower_tree :: AdjTree) <- splitAdjtree adjtree
             lower_tree' :: TTree <- Map.findWithDefault [] lower_tree sims_map
             guard $ snd lower_tree /= lower_tree'
             upper_tree' :: TTree <- Map.findWithDefault [] upper_tree sims_map
             guard $ snd upper_tree /= upper_tree'
             adjtree' :: TTree <- insertBranches [lower_tree'] upper_tree'
             guard $ adjtree' `Set.member` simtrees
             return adjtree'


splitAndPruneTrees :: PruneOpts -> [TTree] -> Map AdjTree (Map [TTree] (Set (TTree, Path)))
splitAndPruneTrees opts base_trees 
    = Map.fromListWith (Map.unionWith Set.union) $
      do (base_tree, adj_path, adj_tree, pruned_children) <- splitAndPrune opts base_trees
         let adj_cat = getToplevelCat adj_tree
         let pruned_cats = map getToplevelCat pruned_children
         return  (((adj_cat, MultiSet.fromList pruned_cats), adj_tree),
                  Map.singleton pruned_children (Set.singleton (base_tree, adj_path)))

splitAndPrune :: PruneOpts -> [TTree] -> [(TTree, Path, TTree, [TTree])]
splitAndPrune opts base_trees =
    do base_tree <- base_trees
       (adj_path, split_tree) <- splitBaseTree base_tree
       (adj_tree, pruned_children) <- getPrunedTrees opts split_tree
       return (base_tree, adj_path, adj_tree, pruned_children)

splitBaseTree :: TTree -> [(Path, TTree)]
splitBaseTree tree@(TNode _ _ children)
    = ([], tree) : [ (n:path, tree') |
                     (n, child) <- zip [0..] children,
                     (path, tree') <- splitBaseTree child ]
splitBaseTree _ = error "Muste.Prune.splitBaseTree: Non-exhaustive pattern match"


getSimTrees :: AdjunctionTrees -> AdjTree -> [TTree]
getSimTrees adjTrees (key, pruned_tree)
    = do let pruned_fun = Grammar.getFunNames pruned_tree
         sim_tree <- Mono.findWithDefault [] key adjTrees 
         let sim_fun = Grammar.getFunNames sim_tree
         guard $ pruned_fun `Set.disjoint` sim_fun
         return sim_tree


splitAdjtree :: AdjTree -> [(AdjTree, AdjTree)]
splitAdjtree ((upper_cat, _holes), base_tree)
    = do (upper_tree, lower_tree) <- split base_tree
         let lower_cat = getToplevelCat lower_tree
         let upper_key = (upper_cat, Grammar.getMetas upper_tree)
         let lower_key = (lower_cat, Grammar.getMetas lower_tree)
         return ((upper_key, upper_tree), (lower_key, lower_tree))
    where split tree@(TNode fun typ children)
              = (TMeta (getToplevelCat tree), tree) :
                do (pre, child, post) <- nondetSplitList children
                   (child', lower_tree) <- split child
                   let children' = pre ++ (child' : post)
                   return (TNode fun typ children', lower_tree)
          split _tree = []


nondetSplitList :: [a] -> [([a], a, [a])]
nondetSplitList [] = []
nondetSplitList (a:bcds) = ([], a, bcds) : [ (a:bs, c, ds) | (bs, c, ds) <- nondetSplitList bcds ]

getToplevelCat :: TTree -> Category
getToplevelCat (TNode _ (Fun cat _) _) = cat
getToplevelCat (TMeta cat) = cat
getToplevelCat _ = error "Muste.Prune.getToplevelCat: Non-exhaustive pattern match"


data PruneOpts = PruneOpts
  { pruneDepth :: Maybe Int
  , pruneSize  :: Maybe Int
  } deriving Show

emptyPruneOpts :: PruneOpts
emptyPruneOpts = PruneOpts Nothing Nothing


-- | Replace all metavariables in a tree with corresponding branches
-- (i.e. they have the correct (same?) type).
--
--  * one branch cannot replace two metavariables this is
--  * nondeterministic, because the tree might contain two metavars
--  * with the same type
insertBranches :: [TTree] -> TTree -> [TTree]
insertBranches branches tree = map fst (ins branches tree)
    where ins [] t = [(t, [])]
          ins bs (TMeta cat) = selectBranch cat bs
          ins bs (TNode fun typ children) = [ (TNode fun typ children', branches') |
                                                    (children', branches') <- inslist bs children ]
          inslist bs [] = [([], bs)]
          inslist bs (t:ts) = [ (t':ts', branches'') |
                                      (t', branches') <- ins bs t,
                                      (ts', branches'') <- inslist branches' ts ]
          selectBranch _ [] = []
          selectBranch cat (tree : trees)
              = [ (tree, trees) | cat == cat' ] ++
                [ (tree', tree:trees') | (tree', trees') <- selectBranch cat trees ]
              where cat' = getToplevelCat tree


getPrunedTrees :: PruneOpts -> TTree -> [(TTree, [TTree])]
getPrunedTrees (PruneOpts depthLimit sizeLimit) tree 
    = [ (tree, branches) | (tree, branches, _) <- pruneTs tree [] 0 0 ]
    where pruneTs :: TTree -> [TTree] -> Int -> Int -> [(TTree, [TTree], Int)]
          pruneTs tree@(TNode fun typ@(Fun cat _) children) branches depth size 
              = (TMeta cat, tree:branches, size) :
                do guard $ depth `less` depthLimit && size `less` sizeLimit
                   (children', branches', size') <- pruneCs children branches (depth+1) (size+1) 
                   return (TNode fun typ children', branches', size')
          pruneTs tree branches _depth size 
              = [(tree, branches, size)]

          pruneCs :: [TTree] -> [TTree] -> Int -> Int -> [([TTree], [TTree], Int)]
          pruneCs [] branches _depth size = return ([], branches, size)
          pruneCs (tree:trees) branches depth size 
              = do (tree', branches', size') <- pruneTs tree branches depth size 
                   (trees', branches'', size'') <- pruneCs trees branches' depth size' 
                   return (tree':trees', branches'', size'')

          value `less` Just limit = value < limit
          _     `less` Nothing    = True

  
