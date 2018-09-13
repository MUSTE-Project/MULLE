{-# Language CPP #-}
{-# OPTIONS_GHC -Wall -Wno-unused-top-binds -Wno-name-shadowing #-}
-- FIXME Should this be an internal module? It's not currently used in
-- @muste-ajax@.
module Muste.Prune
  ( replaceTrees
  , SimTree
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

import Muste.Common

import Muste.Tree (TTree(..), Path, FunType(..), Category)
import qualified Muste.Tree.Internal as Tree
import Muste.Grammar
import qualified Muste.Grammar.Internal as Grammar
import Muste.AdjunctionTrees


-- * Replacing trees

-- | @'replaceTrees' grammar adjTs tree@ finds all trees similar to
-- @tree@ in @adjTs@.  Return a mapping from 'Path''s to the tree you
-- get when you replace one of the valid trees into that given
-- position along with the "cost" of doing so.
replaceTrees
  :: Grammar
  -> AdjunctionTrees
  -> TTree
  -> Map Path (Set (SimTree, TTree))
replaceTrees grammar precomputed tree = M.fromList (go <$> collectSimilarTrees grammar precomputed tree)
  where
  go :: ReplacementTree -> (Path, Set (SimTree, TTree))
  go (path, _, trees) = (path, Set.map (replaceTree tree path) trees)

-- | @'replaceTree' trees@ returns a list of @(cost, isInsertion, t)@
-- where @t@ is a new tree arising from the 'SimTree'.
replaceTree :: TTree -> Path -> SimTree -> (SimTree, TTree)
replaceTree tree path sim@(_, subtree, _, _)
  = (sim, Tree.replaceNode tree path subtree)


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
  :: Grammar
  -> AdjunctionTrees
  -> TTree
  -> [ReplacementTree]
collectSimilarTrees _grammar adjTrees basetree
  = go <$> Tree.getAllPaths basetree
  where
  go :: Path -> ReplacementTree
  go path = (path, tree, Set.fromList simtrees)
    where
      err = error "Muste.Prune.collectSimilarTrees: Incongruence with 'getAllPaths'"
      tree = fromMaybe err $ Tree.selectNode basetree path
      -- Get similar trees.
      simtrees = onlyKeepCheapest $ similarTreesForSubtree tree adjTrees
      -- And then additionally filter some out...

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

-- Profiling has shown me that this function is really heavy.  Quoting
-- the relevant bits:
--                                                                                                                             individual      inherited
-- COST CENTRE                     MODULE                 SRC                                             no.       entries  %time %alloc   %time %alloc
-- collectSimilarTrees.go.simtrees Muste.Prune            src/Muste/Prune.hs:94:7-72                      30643        156    0.0    0.0    46.7   26.9
--  similarTreesForSubtree         Muste.Prune            src/Muste/Prune.hs:(161,1)-(172,39)             30646        156    0.0    0.0    46.6   26.6
--   simTrees                      Muste.Prune            src/Muste/Prune.hs:(177,1)-(181,54)             30647        156    0.0    0.0    46.6   26.6
--    treeDiff                     Muste.Prune            src/Muste/Prune.hs:(300,1)-(303,69)             30698       7172    0.0    0.0     0.0    0.0
--     treeDiff.getNodes           Muste.Prune            src/Muste/Prune.hs:(302,3)-(303,69)             30699     125031    0.0    0.0     0.0    0.0
--     editDistance                Muste.Common           src/Muste/Common.hs:(101,1)-(119,51)            30700       7171    0.0    0.0     0.0    0.0
--      ...
--    insertBranches               Muste.Prune            src/Muste/Prune.hs:(249,1)-(262,89)             30695       7168    0.0    0.0     0.0    0.0
--     ...
--    filterTrees                  Muste.Prune            src/Muste/Prune.hs:(185,1)-(189,14)             30656        597    0.3    0.4    46.6   26.6
--     guardHeuristics             Muste.Prune            src/Muste/Prune.hs:(193,1)-(224,38)             30680   15890368    0.5    0.2    46.2   26.2
--      areDisjoint                Muste.Common           src/Muste/Common.hs:(86,1)-(88,12)              30681   15927504   10.3    6.2    13.9    6.2
--       ...
--      guardHeuristics.funs'      Muste.Prune            src/Muste/Prune.hs:224:3-38                     30685   14407183    0.2    0.0    31.2   18.4
--       getFunctions              Muste.Grammar.Internal src/Muste/Grammar/Internal.hs:(205,1)-(207,21)  30686   14367382   18.4    8.4    31.0   18.4
--        compare                  Muste.Grammar.Internal src/Muste/Grammar/Internal.hs:46:47-49          30863  286693647    1.1    0.0     1.1    0.0
--        getFunctions.getF        Muste.Grammar.Internal src/Muste/Grammar/Internal.hs:(206,11)-(207,21) 30687  143924686   11.5   10.0    11.5   10.0
--      getMetas                   Muste.Grammar.Internal src/Muste/Grammar/Internal.hs:(199,1)-(201,71)  30688    2734008    0.2    0.5     0.6    1.3
--       getMetas.getMetas'        Muste.Grammar.Internal src/Muste/Grammar/Internal.hs:(200,11)-(201,71) 30689   31552618    0.4    0.9     0.4    0.9
--      guardHeuristics.funs       Muste.Prune            src/Muste/Prune.hs:223:3-37                     30682        597    0.0    0.0     0.0    0.0
--       ...
--    pruneTree                    Muste.Prune            src/Muste/Prune.hs:(272,1)-(293,7)              30648        156    0.0    0.0     0.0    0.0
--     ...
--   similarTreesForSubtree.cat    Muste.Prune            src/Muste/Prune.hs:(164,5)-(166,20)             30662        156    0.0    0.0     0.0    0.0
--   similarTreesForSubtree.trees  Muste.Prune            src/Muste/Prune.hs:163:5-57                     30663        156    0.0    0.0     0.0    0.0
--    ...
--  onlyKeepCheapest               Muste.Prune            src/Muste/Prune.hs:119:1-47                     30644          0    0.0    0.0     0.1    0.2
--   ...
similarTreesForSubtree
  :: TTree
  -> AdjunctionTrees
  -> [SimTree]
similarTreesForSubtree tree adjTrees = similiarTrees trees tree
  where
    trees ∷ [TTree]
    trees = fromMaybe errNoCat $ do
      Mono.lookup (cat, metas) adjTrees
    cat = case tree of
      (TNode _ (Fun c _) _) → c
      _ → errNotNode
    metas = Grammar.getMetas tree
    errNoCat = error
      $  "Muste.Prune.similarTreesForSubtree: "
      <> "The tree with the given category and/or metas does not exist."
    errNotNode = error
      $  "Muste.Prune.similarTreesForSubtree: "
      <> "Non-exhaustive pattern match"

-- O(n^3) !!!! I don't think this can be avoided though since the
-- output is bounded by Ω(n^3).
similiarTrees ∷ [TTree] → TTree → [SimTree]
similiarTrees adjTreesForCat tree = do
  (pruned, branches) ← pruneTree tree
  pruned'            ← filterTrees adjTreesForCat pruned
  tree'              ← insertBranches branches pruned'
  pure (tree `treeDiff` tree', tree', pruned, pruned')

-- O(n)
filterTrees ∷ Monad m ⇒ Alternative m ⇒ m TTree → TTree → m TTree
filterTrees trees pruned = do
  -- guard $ noDuplicates funs
  pruned' ← trees
  guard $ heuristics pruned pruned'
  pure pruned'

-- | Various heuristics used for filtering out results.
heuristics ∷ TTree → TTree → Bool
heuristics pruned pruned' = and
  [ True
#ifdef PRUNE_ALT_1A
  ---- Alternative 1a: the root must change.
  , not (sameRoot pruned pruned') --- ***
#endif
#ifdef PRUNE_ALT_1B
  ---- Alternative 1b: it's ok if two different children change.
  , not (exactlyOneChildDiffers pruned pruned') -- ***
#endif
#ifdef PRUNE_ALT_1C
  ---- Alternative 1c: the pruned trees should not share any functions.
  , noDuplicates funs' -- ***
#endif
#ifdef PRUNE_ALT_1D
  -- This is really heavy!  The call to 'Grammar.getFunctions' force
  -- us to traverse the whole structure.  Perhaps if we could build up
  -- the results and do some clever memoization.
  , funs `disjoint` funs'
#endif
#ifdef PRUNE_ALT_2A
  ---- Alternative 2a: all branches are put back into the new tree.
  , Grammar.getMetas pruned == Grammar.getMetas pruned'
#endif
#ifdef PRUNE_ALT_2B
  ---- Alternative 2b: some branches may be removed from the new tree.
  , isSubList metas (getMetas pruned') -- ***
#endif
  ]
  where
  funs  = Grammar.getFunctions pruned
  funs' = Grammar.getFunctions pruned'

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
pruneTree :: TTree -> [(TTree, [TTree])]
pruneTree tree = [(t, bs) | (t, bs, _) <- pt mempty tree]
  where
  pt ∷ Set Category → TTree → [(TTree, [TTree], Set Category)]
  pt visited = \case
    tree@(TNode _ _ []) → [(tree, [], visited)]
    tree@(TNode fun typ@(Fun cat _) children)
      → (TMeta cat, [tree], visited) :
        [ (TNode fun typ children', branches', visited')
        | cat `notElem` visited
        , (children', branches', visited') ← pc (Set.insert cat visited) children
        ]
    _ → error "Muste.Prune.pruneTree: Incomplete pattern match"
  pc ∷ Set Category → [TTree] → [([TTree], [TTree], Set Category)]
  pc visited = \case
    []     → [([], [], visited)]
    (t:ts) →
      [ (t'  : ts' , bs' <> bs'', visited'')
      | (t'  , bs' , _visited') ← pt visited t
      -- Should visited be visited'? Or perhaps visited'' above should
      -- be the union of the two?
      , (ts' , bs'', visited'') ← pc visited ts
      ]

-- | Edit distance between trees.
--
-- This is calculated by the Levenshtein distance between the list of
-- function nodes in each of the trees
treeDiff :: TTree -> TTree -> Int
treeDiff s t = getNodes s `editDistance` getNodes t
  where
  getNodes (TMeta cat) = ["?" ++ cat]
  getNodes (TNode fun _ children) = fun : concatMap getNodes children
