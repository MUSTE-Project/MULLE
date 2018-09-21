{-# OPTIONS_GHC -Wall -Wno-unused-top-binds -Wno-name-shadowing #-}
{-# Language DerivingStrategies, ConstraintKinds #-}
-- FIXME Should this be an internal module? It's not currently used in
-- @muste-ajax@.
module Muste.Prune
  ( replaceTrees
  , SimTree
  , PruneOpts(..)
  ) where

import Prelude ()
import Muste.Prelude
import Data.Map (Map)
import qualified Data.Containers as Mono
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as Set
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet
import Control.Monad.Reader
import Data.Functor.Identity

import Muste.Common

import Muste.Tree (TTree(..), Path, FunType(..), Category)
import qualified Muste.Tree.Internal as Tree
import Muste.Grammar hiding (tree)
import qualified Muste.Grammar.Internal as Grammar
import Muste.AdjunctionTrees hiding (BuilderInfo(..))


-- * Replacing trees

-- | @'replaceTrees' grammar adjTs tree@ finds all trees similar to
-- @tree@ in @adjTs@.  Return a mapping from 'Path''s to the tree you
-- get when you replace one of the valid trees into that given
-- position along with the "cost" of doing so.
replaceTrees
  ∷ Grammar         -- ^ The grammar
  → AdjunctionTrees -- ^ The pre computed adjunction trees
  → TTree           -- ^ The tree where we do the replacements
  → Set TTree
replaceTrees g adj t
  -- TODO Add the 'PruneOpts' as an argument!
  = runPrunerI pruner (mempty @PruneOpts)
  where
  pruner ∷ PrunerI (Set TTree)
  pruner = replaceTreesM g adj t

replaceTreesM
  ∷ Pruner m
  ⇒ Grammar
  → AdjunctionTrees
  → TTree
  → m (Set TTree)
replaceTreesM grammar precomputed tree = do
  simtrees ← collectSimilarTrees grammar precomputed tree
  pure
    $   mconcat
    $   go
    <$> simtrees
  where
  go :: ReplacementTree -> Set TTree
  go (path, _, trees) = Set.map (snd . replaceTree tree path) trees

-- | @'replaceTree' trees@ returns a list of @(cost, isInsertion, t)@
-- where @t@ is a new tree arising from the 'SimTree'.
replaceTree :: TTree -> Path -> SimTree -> (SimTree, TTree)
replaceTree tree path sim@(_, subtree, _, _)
  = (sim, Tree.replaceNode tree path subtree)

data PruneOpts = PruneOpts
  { searchDepth ∷ Maybe Int
  }

instance Semigroup PruneOpts where
  PruneOpts a <> PruneOpts b = PruneOpts $ (+) <$> a <*> b

instance Monoid PruneOpts where
  mempty = PruneOpts empty

type Pruner m =
  ( MonadReader PruneOpts m
  )

-- | The monad used for creating similar trees.  It's a bit of a
-- misnomer because it does more than prune trees.
newtype PrunerT m a = PrunerT { unPrunerT ∷ ReaderT PruneOpts m a }

deriving newtype instance Functor m ⇒ Functor (PrunerT m)
deriving newtype instance Monad m   ⇒ Applicative (PrunerT m)
deriving newtype instance Monad m   ⇒ Monad (PrunerT m)
deriving newtype instance Monad m   ⇒ MonadReader PruneOpts (PrunerT m)

type PrunerI a = PrunerT Identity a

runPrunerI ∷ PrunerI a → PruneOpts → a
runPrunerI = runReader . unPrunerT

askSearchDepth ∷ Pruner m ⇒ m (Maybe Int)
askSearchDepth = asks searchDepth


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
  ⇒ Grammar
  → AdjunctionTrees
  → TTree
  → m [ReplacementTree]
collectSimilarTrees _grammar adjTrees basetree
  = traverse go $ Tree.getAllPaths basetree
  where
  go ∷ Pruner m ⇒ Path -> m ReplacementTree
  go path = do
    simtrees ← getSimTrees
    pure (path, tree, Set.fromList simtrees)
    where
      err = error "Muste.Prune.collectSimilarTrees: Incongruence with 'getAllPaths'"
      tree = fromMaybe err $ Tree.selectNode basetree path
      getSimTrees ∷ Pruner m ⇒ m [SimTree]
      getSimTrees = onlyKeepCheapest <$> similarTreesForSubtree tree adjTrees

-- FIXME Quadratic in the length of 'simtrees'.  Even though this is
-- quadratic, profiling shows that this is negliciable.
--
-- FIXME Shouldn't the condition that the edge between two nodes is
-- less than or equal to the cost be vacously true? -- No! This is the
-- whole point.  Consider the following graph of costs:
--
--     orig: [(a, 2), (b, 4)]
--     a   : [(b, 1)]
--
-- After calculating the shortest path (which I assume is what is
-- stored in a 'SimTree'.  We get the folloing graph:
--
--     orig: [(a, 2), (b, 3)]
--
-- And here it can be seen that the shortest path from @orig@ to @b@
-- is cheaper than the edge cost.  So therefore, we must *exclude* the
-- edge @(orig, b)@ from the result.
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

-- Profiling reveals that this function is really heavy.  Quoting the
-- relevant bits:
--
--                                                                                                     individual      inherited
--     COST CENTRE                                 MODULE                         no.       entries  %time %alloc   %time %alloc
--     collectSimilarTrees                         Muste.Prune                    20648          2    0.0    0.0    32.6   45.3
--      collectSimilarTrees.go                     Muste.Prune                    20651         29    0.0    0.0    32.5   45.3
--       compare                                   Muste.Tree.Internal            20955        437    0.0    0.0     0.0    0.0
--        compare                                  Muste.Tree.Internal            20956        264    0.0    0.0     0.0    0.0
--       collectSimilarTrees.go.simtrees           Muste.Prune                    20664         29    0.0    0.0    32.5   45.3
--        similarTreesForSubtree                   Muste.Prune                    20668         29    0.0    0.0    32.2   44.8
--         similarTreesForSubtree.cat              Muste.Prune                    20835         29    0.0    0.0     0.0    0.0
--         similarTreesForSubtree.metas            Muste.Prune                    20838         29    0.0    0.0     0.0    0.0
--          ...
--         similarTreesForSubtree.trees            Muste.Prune                    20731         29    0.0    0.0     0.0    0.0
--          ...
--         similarTrees                            Muste.Prune                    20669         29    0.0    0.0    32.2   44.8
--          insertBranches                         Muste.Prune                    20920        461    0.0    0.0     0.0    0.0
--           insertBranches.ins                    Muste.Prune                    20921        461    0.0    0.0     0.0    0.0
--          treeDiff                               Muste.Prune                    20923        461    0.0    0.0     0.0    0.0
--           ...
--          filterTrees                            Muste.Prune                    20730        139    0.1    0.0    32.2   44.7
--           heuristics                            Muste.Prune                    20846     417034    0.2    0.2    32.1   44.7
--            disjoint                             Muste.Prune                    20847     417034    0.1    0.2     8.7    6.6
--             ...
--            heuristics.funs'                     Muste.Prune                    20887     389737    0.1    0.0    22.6   37.3
--             getFunctions                        Muste.Grammar.Internal         20888          0    1.2    0.0    22.5   37.3
--              getFunctions.\                     Muste.Grammar.Internal         20889    4065372    3.8   15.4    21.3   37.3
--               mconcat                           Data.MultiSet                  20890    4065372    0.4    0.0    17.4   21.9
--                unions                           Data.MultiSet                  20891    4065372    0.3    0.0    17.0   21.9
--                 foldlStrict                     Data.MultiSet                  20892   11806379    1.9    0.0    16.7   21.9
--                  foldlStrict.z'                 Data.MultiSet                  20893    7741007    0.7    0.0    14.9   21.9
--                   union                         Data.MultiSet                  20894    7741007   11.1   21.9    14.2   21.9
--                    compare                      Muste.Grammar.Internal         20896    9833223    3.1    0.0     3.1    0.0
--               singleton                         Data.MultiSet                  20895    4065372    0.0    0.0     0.0    0.0
--            ==                                   Data.MultiSet                  20857      41678    0.0    0.0     0.0    0.0
--             unMS                                Data.MultiSet                  20867      83356    0.0    0.0     0.0    0.0
--            heuristics.funs                      Muste.Prune                    20852        139    0.0    0.0     0.0    0.0
--             ...
--            getMetas                             Muste.Grammar.Internal         20868          0    0.1    0.0     0.6    0.6
--             ...
--          pruneTree                              Muste.Prune                    20670         29    0.0    0.0     0.0    0.0
--           ...
--        onlyKeepCheapest                         Muste.Prune                    20666          0    0.0    0.0     0.3    0.6
--         ...
--       collectSimilarTrees.go.tree               Muste.Prune                    20672         29    0.0    0.0     0.0    0.0
--        ...
--      getAllPaths                                Muste.Tree.Internal            20649          2    0.0    0.0     0.0    0.0
--       ...

similarTreesForSubtree
  ∷ Pruner m
  ⇒ TTree
  → AdjunctionTrees
  → m [SimTree]
similarTreesForSubtree tree adjTrees = similarTrees trees tree
  where
    trees ∷ Map (MultiSet Category) [(TTree, MultiSet Rule)]
    trees
      = M.fromListWith mappend
      $ fmap (\t → (Grammar.getMetas t, pure (t, Grammar.getFunctions t)))
      $ fromMaybe mempty
      $ Mono.lookup (cat, metas) adjTrees
    cat = case tree of
      (TNode _ (Fun c _) _) → c
      _ → errNotNode
    metas = Grammar.getMetas tree
    errNotNode = error
      $  "Muste.Prune.similarTreesForSubtree: "
      <> "Non-exhaustive pattern match"

-- O(n^3) !!!! I don't think this can be avoided though since the
-- output is bounded by Ω(n^3).
similarTrees
  ∷ Pruner m
  ⇒ Map (MultiSet Category) [(TTree, MultiSet Rule)]
  → TTree
  → m [SimTree]
similarTrees byMetas tree = do
  prunedTrees ← pruneTree tree
  pure $ do
    (pruned, branches) ← prunedTrees
    pruned'            ← filterTrees byMetas pruned
    tree'              ← insertBranches branches pruned'
    pure (tree `treeDiff` tree', tree', pruned, pruned')

-- m ~ [] ⇒ runtime = O(n)
filterTrees
  ∷ Monad m
  ⇒ Alternative m
  ⇒ Map (MultiSet Category) (m (TTree, MultiSet Rule))
  → TTree
  → m TTree
filterTrees byMetas pruned =
  case M.lookup (Grammar.getMetas pruned) byMetas of
    Nothing → empty
    Just xs → do
      (pruned', funs) ← xs
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

-- FIXME Certainly something wrong with the wording here "up to a
-- given depth". There is no parameter so surely it should be "up to a
-- fixed depth". I can't verify that this is the case either though
-- from quickly glancing at the implementation.
-- | Calculates all possible pruned trees up to a given depth.  A
-- pruned tree consists of a tree with metavariables and a list of all
-- the pruned branches (subtrees).
pruneTree :: Pruner m ⇒ TTree -> m [(TTree, [TTree])]
pruneTree tree = do
  d ← askSearchDepth
  pure [(t, bs) | (t, bs, _) <- pt d mempty tree]
  where
  pt ∷ Maybe Int → Set Category → TTree → [(TTree, [TTree], Set Category)]
  pt d visited
    | dun d = mempty
    | otherwise = \case
      tree@(TNode _ _ []) → [(tree, [], visited)]
      tree@(TNode fun typ@(Fun cat _) children)
        → (TMeta cat, [tree], visited) :
          [ (TNode fun typ children', branches', visited')
          | cat `notElem` visited
          , (children', branches', visited') ← pc d (Set.insert cat visited) children
          ]
      _ → error "Muste.Prune.pruneTree: Incomplete pattern match"
  pc ∷ Maybe Int → Set Category → [TTree] → [([TTree], [TTree], Set Category)]
  pc d visited = \case
    []     → [([], [], visited)]
    (t:ts) →
      [ (t'  : ts' , bs' <> bs'', visited'')
      | (t'  , bs' , _visited') ← pt (pred <$> d) visited t
      -- Should visited be visited'? Or perhaps visited'' above should
      -- be the union of the two?
      , (ts' , bs'', visited'') ← pc d visited ts
      ]
  dun ∷ Maybe Int → Bool
  dun = fromMaybe False . fmap (<= 0)

-- | Edit distance between trees.
--
-- This is calculated by the Levenshtein distance between the list of
-- function nodes in each of the trees
treeDiff :: TTree -> TTree -> Int
treeDiff s t = getNodes s `editDistance` getNodes t
  where
  getNodes (TMeta cat) = ["?" ++ cat]
  getNodes (TNode fun _ children) = fun : concatMap getNodes children
