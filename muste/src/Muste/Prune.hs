{-# OPTIONS_GHC -Wall -Wno-unused-top-binds -Wno-name-shadowing #-}
{-# Language DerivingStrategies, ConstraintKinds, RecordWildCards,
  OverloadedStrings #-}
-- FIXME Should this be an internal module? It's not currently used in
-- @muste-ajax@.
module Muste.Prune
  ( replaceTrees
  , SimTree
  , PruneOpts(..)
  ) where

import Prelude ()
import Muste.Prelude
import qualified Data.Containers as Mono
import Data.Set (Set)
import qualified Data.Set as Set
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet
import Control.Monad.Reader
import Data.Functor.Identity

import Muste.Common

import Muste.Tree (TTree(..), Path, FunType(..), Category)
import qualified Muste.Tree.Internal as Tree
import Muste.Grammar
import qualified Muste.Grammar.Internal as Grammar
import Muste.AdjunctionTrees hiding (BuilderInfo(..))


-- * Replacing trees

-- | @'replaceTrees' grammar adjTs tree@ finds all trees similar to
-- @tree@ in @adjTs@.  Return a mapping from 'Path''s to the tree you
-- get when you replace one of the valid trees into that given
-- position along with the "cost" of doing so.
replaceTrees
  ∷ PruneOpts       -- ^ Options controlling the pruning algorithm
  → Grammar         -- ^ The grammar
  → AdjunctionTrees -- ^ The pre computed adjunction trees
  → TTree           -- ^ The tree where we do the replacements
  → Set TTree
replaceTrees opts g adj t
  = runPrunerI pruner env
  where
  pruner ∷ PrunerI (Set TTree)
  pruner = replaceTreesM
  env ∷ Env
  env = Env
    { pruneOpts   = opts
    , grammar     = g
    , precomputed = adj
    , baseTree    = t
    }

replaceTreesM
  ∷ Pruner m
  ⇒ m (Set TTree)
replaceTreesM = do
  tree ← askBaseTree
  let go ∷ ReplacementTree → Set TTree
      go (path, _, trees) = Set.map (snd . replaceTree tree path) trees
  simtrees ← collectSimilarTrees
  pure
    $   mconcat
    $   go
    <$> simtrees

-- | @'replaceTree' trees@ returns a list of @(cost, isInsertion, t)@
-- where @t@ is a new tree arising from the 'SimTree'.
replaceTree :: TTree -> Path -> SimTree -> (SimTree, TTree)
replaceTree tree path sim@(_, subtree, _, _)
  = (sim, Tree.replaceNode tree path subtree)

data PruneOpts = PruneOpts
  { searchDepth ∷ Maybe Int
  , searchSize  ∷ Maybe Int
  }

instance Semigroup PruneOpts where
  PruneOpts a0 a1 <> PruneOpts b0 b1
    = PruneOpts (a0 <+> b0) (a1 <+> b1)
    where
    a <+> b = (+) <$> a <*> b

instance Monoid PruneOpts where
  mempty = PruneOpts empty empty

data Env = Env
  { pruneOpts   ∷ PruneOpts
  , grammar     ∷ Grammar         -- ^ The grammar
  , precomputed ∷ AdjunctionTrees -- ^ The pre computed adjunction trees
  , baseTree    ∷ TTree           -- ^ The tree where we do the replacements
  }

type Pruner m =
  ( MonadReader Env m
  )

-- | The monad used for creating similar trees.  It's a bit of a
-- misnomer because it does more than prune trees.
newtype PrunerT m a = PrunerT { unPrunerT ∷ ReaderT Env m a }

deriving newtype instance Functor m ⇒ Functor (PrunerT m)
deriving newtype instance Monad m   ⇒ Applicative (PrunerT m)
deriving newtype instance Monad m   ⇒ Monad (PrunerT m)
deriving newtype instance Monad m   ⇒ MonadReader Env (PrunerT m)

type PrunerI a = PrunerT Identity a

runPrunerI ∷ PrunerI a → Env → a
runPrunerI = runReader . unPrunerT

askSearchDepth ∷ Pruner m ⇒ m (Maybe Int)
askSearchDepth = asks (\Env{pruneOpts=PruneOpts{..}} → searchDepth)

askPruneOpts ∷ Pruner m ⇒ m PruneOpts
askPruneOpts = asks (\Env{..} → pruneOpts)

askGrammar ∷ Pruner m ⇒ m Grammar
askGrammar = asks (\Env{..} → grammar)

askPrecomputed ∷ Pruner m ⇒ m AdjunctionTrees
askPrecomputed = asks (\Env{..} → precomputed)

askBaseTree ∷ Pruner m ⇒ m TTree
askBaseTree = asks (\Env{..} → baseTree)


-- * Pruning

-- | A simtree is calculated given a pair @(path, origTree)@ of
-- @('Path', 'TTree')@.  It consists of @(cost, tree, pruned,
-- pruned')@ where.
--
--  * @cost@ is the edit distance between @tree@ and @origTree@
--  * @tree@ is the new similar subtree.
--  * @pruned@ is the original pruned subtree (at position @path@)
--  * @pruned'@ is the new similar pruned subtree (at position @path@)
type SimTree = (Int, TTree, TTree, TTree)

-- | A replacement tree describes possible replacements in a sub tree
-- with respect to some originating tree.  The original tree is not
-- retrievable from this type, but values of 'ReplacementTree' are
-- calculated (from 'collectSimilarTrees') given some initial tree.
--
-- Replacements are done at the subtree 'originalSubTree', and the
-- possible replacements are given by 'replacements'.
type ReplacementTree = (Path, TTree, Set SimTree)

-- FIXME We are not using the grammar.  Is this a mistake?
-- | @'collectSimilarTrees' grammar adjTrees baseTree@ grammar
-- adjTrees baseTree@ collects all similar trees of a given
-- @baseTree@, according to a 'Grammar' @grammar@, by first pruning
-- the tree, then generating all similar pruned trees, then putting
-- all pruned branches back in.  The candidates where we look for
-- similar trees is in @adjTrees@.
--
-- A simliar tree is given by @ReplacementTree@.
collectSimilarTrees
  ∷ Pruner m
  ⇒ m [ReplacementTree]
collectSimilarTrees = do
  basetree ← askBaseTree
  let
    go ∷ Pruner m ⇒ Path -> m ReplacementTree
    go path = do
      simtrees ← getSimTrees
      pure (path, tree, Set.fromList simtrees)
      where
        err = error "Muste.Prune.collectSimilarTrees: Incongruence with 'getAllPaths'"
        tree = fromMaybe err $ Tree.selectNode basetree path
        getSimTrees ∷ Pruner m ⇒ m [SimTree]
        getSimTrees = onlyKeepCheapest <$> similarTreesForSubtree tree
  traverse go $ Tree.getAllPaths basetree

-- | If the direct edge to another node is more expensive than the
-- shortest path, then it means we can reach this tree via a series of
-- other edits, so we exclude this.
onlyKeepCheapest :: [SimTree] -> [SimTree]
onlyKeepCheapest = keepWith directMoreExpensive

keepWith
  ∷ Monad f ⇒ Foldable f ⇒ Alternative f
  ⇒ (a → a → Bool) → f a -> f a
keepWith p xs = do
  x <- xs
  guard $ not $ or $ do
    x' <- xs
    pure $ x `p` x'
  pure x

-- | Checks if the direct edge between two trees is more expensive
-- than the shortest path.
directMoreExpensive ∷ SimTree → SimTree → Bool
directMoreExpensive (cost, t, _, _) (cost', t', _, _)
  = cost' < cost && t' `treeDiff` t < cost

similarTreesForSubtree ∷ Pruner m ⇒ TTree → m [SimTree]
similarTreesForSubtree tree = do
  adjTrees ← askPrecomputed
  let
    cat = case tree of
      (TNode _ (Fun c _) _) → c
      _ → errNotNode
    errNotNode = error
      $  "Muste.Prune.similarTreesForSubtree: "
      <> "Non-exhaustive pattern match"
  similarTrees cat adjTrees tree

-- O(n^3) !!!! I don't think this can be avoided though since the
-- output is bounded by Ω(n^3).
similarTrees ∷ Pruner m ⇒ Category → AdjunctionTrees → TTree → m [SimTree]
similarTrees cat adjTrees tree = do
  prunedTrees ← pruneTree tree
  pure $ do
    (pruned, branches) ← prunedTrees
    let metas = Grammar.getMetas pruned
    byMetas            ← maybeToList $ Mono.lookup (cat, metas) adjTrees
    pruned'            ← filterTrees byMetas pruned
    tree'              ← insertBranches branches pruned'
    pure (tree `treeDiff` tree', tree', pruned, pruned')

maybeToList :: Maybe a -> [a]
maybeToList (Just a) = [a]
maybeToList _ = []

-- m ~ [] ⇒ runtime = O(n)
filterTrees ∷ Monad m ⇒ Alternative m ⇒ m TTree → TTree → m TTree
filterTrees byMetas pruned = do
  pruned' ← byMetas
  let funs = Grammar.getFunctions pruned'
  guard $ heuristics pruned funs
  pure pruned'

-- | Various heuristics used for filtering out results.
heuristics ∷ TTree → MultiSet Rule → Bool
heuristics pruned funs = Grammar.getFunctions pruned `disjoint` funs

-- | @True@ if two trees have the same root.
sameRoot :: TTree -> TTree -> Bool
sameRoot (TNode fun _ _) (TNode fun' _ _) | fun == fun' = True
sameRoot (TMeta cat) (TMeta cat') | cat == cat' = True
sameRoot _ _ = False

disjoint ∷ Ord a ⇒ MultiSet a → MultiSet a → Bool
disjoint a b = MultiSet.null $ MultiSet.intersection a b

-- | @True@ if two trees have the same root, and exactly one child
-- differs.
exactlyOneChildDiffers :: TTree -> TTree -> Bool
exactlyOneChildDiffers (TNode fun _ children) (TNode fun' _ children')
    | fun == fun' = difftrees children children'
    where difftrees (t:ts) (t':ts') | t == t' = difftrees ts ts'
                                    | otherwise = ts == ts'
          difftrees _ _ = False
exactlyOneChildDiffers _ _ = False

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
          selectBranch cat (tree@(TNode _ (Fun cat' _) _) : trees)
              = [ (tree, trees) | cat == cat' ] ++
                [ (tree', tree:trees') | (tree', trees') <- selectBranch cat trees ]
          selectBranch _ _ = error "Muste.Prune.insertBranches: Incomplete pattern match"


-- | Calculates all possible pruned trees, possibly limited by a
-- given depth or tree size. A pruned tree consists of a tree with
-- metavariables and a list of all the pruned branches (subtrees).
pruneTree :: Pruner m ⇒ TTree -> m [(TTree, [TTree])]
pruneTree tree = do
  opts <- askPruneOpts
  pure $ getPrunedTrees opts tree

getPrunedTrees :: PruneOpts -> TTree -> [(TTree, [TTree])]
getPrunedTrees (PruneOpts depthLimit sizeLimit) tree 
    = [ (tree, branches) | (tree, branches, _, _) <- pruneTs tree [] 0 0 [] ]
    where pruneTs :: TTree -> [TTree] -> Int -> Int -> [Category] -> [(TTree, [TTree], Int, [Category])]
          pruneTs tree@(TNode fun typ@(Fun cat _) children) branches depth size visited =
              (TMeta cat, tree:branches, size, visited) :
              do guard $ cat `notElem` visited
                 guardLimit depthLimit depth
                 guardLimit sizeLimit size
                 (children', branches', size', visited') <- pruneCs children branches (depth+1) (size+1) (cat : visited)
                 return (TNode fun typ children', branches', size', visited')
          pruneTs _ _ _ _ _ = error "Muste.Prune.getPrunedTrees: Incomplete pattern match"

          pruneCs :: [TTree] -> [TTree] -> Int -> Int -> [Category] -> [([TTree], [TTree], Int, [Category])]
          pruneCs [] branches _depth size visited = return ([], branches, size, visited)
          pruneCs (tree:trees) branches depth size visited =
              do (tree', branches', size', visited') <- pruneTs tree branches depth size visited
                 (trees', branches'', size'', visited'') <- pruneCs trees branches' depth size' visited'
                 return (tree':trees', branches'', size'', visited'')

          guardLimit (Just limit) value = guard $ value < limit
          guardLimit Nothing _ = return ()
  

-- | Edit distance between trees.
--
-- This is calculated by the Levenshtein distance between the list of
-- function nodes in each of the trees
treeDiff :: TTree -> TTree -> Int
treeDiff s t = getNodes s `editDistance` getNodes t
  where
  getNodes (TMeta cat) = ["?" <> cat]
  getNodes (TNode fun _ children) = fun : concatMap getNodes children
