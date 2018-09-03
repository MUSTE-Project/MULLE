{-# Language CPP #-}
{-# OPTIONS_GHC -Wall -Wno-unused-top-binds -Wno-name-shadowing #-}
-- FIXME Should this be an internal module? It's not currently used in
-- @muste-ajax@.
module Muste.Prune
  ( getAdjunctionTrees
  , replaceTrees
  , SimTree
  ) where

import Prelude ()
import Muste.Prelude
import Data.List (sort)
import qualified Data.Containers as Mono
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as Set

import Muste.Common
import Muste.Tree (TTree(..), Path, FunType(..), Category)
import qualified Muste.Tree.Internal as Tree
import Muste.Grammar
import Muste.Grammar.Internal (Rule(Function))
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

-- FIXME We are not using the grammar. Is this a mistake
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
--
-- COST CENTRE                            entries  %time %alloc   %time %alloc
--
--     similarTreesForSubtree                  10    0.7    0.9    42.9   72.2
--      areDisjoint                       3813390    6.0    2.3    10.9    2.3
--       ==                               3752120    2.5    0.0     3.7    0.0
--        ==                               568487    1.1    0.0     1.1    0.0
--       <                                3183633    1.3    0.0     1.3    0.0
--      similarTreesForSubtree.funs'       569826    0.1    0.0    30.0   66.0
--       getFunctions                      569826   12.8   29.1    29.9   66.0
--        compare                         9820790    5.2    0.0     5.2    0.0
--        getFunctions.getF               6681507   11.9   36.9    11.9   36.9
--      getMetas                            61270    0.6    1.0     1.2    2.9
--       getMetas.getMetas'                695042    0.6    1.9     0.6    1.9
--      insertBranches                        136    0.0    0.0     0.0    0.0
--       insertBranches.ins                   178    0.0    0.0     0.0    0.0
--        insertBranches.inslist               81    0.0    0.0     0.0    0.0
--        insertBranches.selectBranch          48    0.0    0.0     0.0    0.0
similarTreesForSubtree
  :: TTree
  -> AdjunctionTrees
  -> [SimTree]
similarTreesForSubtree tree adjTrees = simTrees trees tree
  where
    trees = fromMaybe errNoCat $ Mono.lookup cat adjTrees
    cat = case tree of
      (TNode _ (Fun c _) _) → c
      _ → errNotNode
    errNoCat = error
      $  "Muste.Prune.similarTreesForSubtree: "
      <> "The given category does not exist in the adjunction tree"
    errNotNode = error
      $  "Muste.Prune.similarTreesForSubtree: "
      <> "Non-exhaustive pattern match"

-- O(n^3) !!!! I don't think this can be avoided though since the
-- output is bounded by Ω(n^3).
simTrees ∷ [TTree] → TTree → [SimTree]
simTrees adjTreesForCat tree = do
  (pruned, branches) ← pruneTree tree
  pruned'            ← filterTrees adjTreesForCat pruned
  tree'              ← insertBranches branches pruned'
  pure (tree `treeDiff` tree', tree', pruned, pruned')

-- O(n)
filterTrees ∷ Monad m ⇒ Alternative m ⇒ m TTree → TTree → m TTree
filterTrees trees pruned = do
  -- guard $ noDuplicates funs
  pruned' ← trees
  guardHeuristics pruned pruned'
  pure pruned'

-- | Various heuristics used for filtering out results.
guardHeuristics ∷ Alternative f ⇒ TTree → TTree → f ()
guardHeuristics pruned pruned' = guard $ and
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
  , funs `areDisjoint` funs'
#endif
#ifdef PRUNE_ALT_2A
  ---- Alternative 2a: all branches are put back into the new tree.
  , getMetas pruned == getMetas pruned'
#endif
#ifdef PRUNE_ALT_2B
  ---- Alternative 2b: some branches may be removed from the new tree.
  , isSubList metas (getMetas pruned') -- ***
#endif
  ]
  where
  funs  = getFunctions pruned
  funs' = getFunctions pruned'

-- | Returns an ordered list with all functions in a tree.
getFunctions :: TTree -> [Rule]
getFunctions tree = sort (getF tree)
    where getF (TNode fun typ children) = Function fun typ : concatMap getF children
          getF _ = []

-- | @True@ if two trees have the same root.
sameRoot :: TTree -> TTree -> Bool
sameRoot (TNode fun _ _) (TNode fun' _ _) | fun == fun' = True
sameRoot (TMeta cat) (TMeta cat') | cat == cat' = True
sameRoot _ _ = False

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

-- | Calculates a sorted list of the categories of all metavariables
-- in a tree. Note that the list may contain duplicates
getMetas :: TTree -> [Category]
getMetas tree = sort (getMetas' tree)
    where getMetas' (TMeta cat) = [cat]
          getMetas' (TNode _ _ children) = concatMap getMetas' children

-- FIXME Certainly something wrong with the wording here "up to a
-- given depth". There is no parameter so surely it should be "up to a
-- fixed depth". I can't verify that this is the case either though
-- from quickly glancing at the implementation.
-- | Calculates all possible pruned trees up to a given depth. A
-- pruned tree consists of a tree with metavariables and a list of all
-- the pruned branches (subtrees).
pruneTree :: TTree -> [(TTree, [TTree])]
pruneTree tree = [(t, bs) | (t, bs, _) <- pt [] tree]
    where pt visited tree@(TNode _ _ []) = [(tree, [], visited)]
          pt visited tree@(TNode fun typ@(Fun cat _) children)
              = (TMeta cat, [tree], visited) :
                [ (tree', branches', visited') |
                  cat `notElem` visited,
                  (children', branches', visited') <- pc (cat:visited) children,
                  let tree' = TNode fun typ children'
                ]
          pt _ _ = error "Muste.Prune.pruneTree: Incomplete pattern match"
          pc visited [] = [([], [], visited)]
          pc visited (t:ts) = [ (t':ts', bs' ++ bs'', visited'') |
                                (t', bs', _visited') <- pt visited t,
                                (ts', bs'', visited'') <- pc visited ts ]

-- | Edit distance between trees.
--
-- This is calculated by the Levenshtein distance between the list of
-- function nodes in each of the trees
treeDiff :: TTree -> TTree -> Int
treeDiff s t = getNodes s `editDistance` getNodes t
  where
  getNodes (TMeta cat) = ["?" ++ cat]
  getNodes (TNode fun _ children) = fun : concatMap getNodes children


-- * Creating adjunction trees.

-- Profiling has shown me that this function is really heavy.  Quoting the relevant bits:
--
-- COST CENTRE                                                               entries  %time %alloc   %time %alloc
--     getAdjunctionTrees                                                    1        0.0    0.0     4.6   10.2
--      getAdjunctionTrees.\                                                 29       0.0    0.2     4.6   10.2
--       getAdjunctionTrees.adjTrees                                         54085    0.6    1.1     4.6   10.0
--        getAdjunctionTrees.adjChildren                                     341021   0.9    2.4     3.1    8.8
--         treeIsRecursive                                                   281519   0.3    0.2     2.3    6.3
--          getMetas                                                         227463   0.8    2.6     1.7    5.1
--           getMetas.getMetas'                                              1184075  1.0    2.6     1.0    2.6
--          getFunctions                                                     62894    0.2    0.6     0.2    1.0
--           getFunctions.getF                                               98140    0.0    0.3     0.0    0.3
--           compare                                                         57024    0.0    0.0     0.0    0.0
--        getAdjunctionTrees.getRulesFor                                     18947    0.9    0.1     0.9    0.1
-- | Finds all @AdjunctionTrees@ from a specified 'Grammar'.  That is;
-- a mapping from a @Category@ to all trees in the specified 'Grammar'
-- that have this type.
getAdjunctionTrees :: Grammar -> AdjunctionTrees
getAdjunctionTrees grammar = Mono.mapFromList ((\cat -> (cat, map fst (adjTrees getRulesFor cat []))) <$> allCats)
  where
  allRules :: Map String [Rule]
  allRules = M.fromListWith mappend $ catRule <$> Grammar.getAllRules grammar
  catRule ∷ Rule → (String, [Rule])
  catRule r@(Function _ (Fun c _)) = (c, pure r)
  catRule _ = error "Non-exhaustive pattern match"
  allCats :: [String]
  allCats = M.keys allRules
  getRulesFor :: String -> [Rule]
  getRulesFor cat = M.findWithDefault mempty cat allRules

-- The next two functions are mutually recursive.
adjTrees :: (String → [Rule]) → String -> [String] -> [(TTree, [String])]
adjTrees getRulesFor cat visited = (TMeta cat, visited) : do
  guard $ cat `notElem` visited
  (Function fun typ@(Fun _ childcats)) <- getRulesFor cat
  (children, visited') <- adjChildren getRulesFor childcats (cat:visited)
  pure (TNode fun typ children, visited')

adjChildren :: (String → [Rule]) → [String] -> [String] -> [([TTree], [String])]
adjChildren _getRulesFor [] visited = [([], visited)]
adjChildren getRulesFor (cat:cats) visited = do
  (tree, visited') <- adjTrees getRulesFor cat visited
  guard $ not $ treeIsRecursive tree
  (trees, visited'') <- adjChildren getRulesFor cats visited'
  pure (tree:trees, visited'')

treeIsRecursive :: TTree -> Bool
treeIsRecursive tree@(TNode _ (Fun cat _) children) =
    case getMetas tree of
      [] -> cat `elem` [cat' | Function _ (Fun cat' _) <- concatMap getFunctions children]
      [cat'] -> cat == cat'
      _ -> False
treeIsRecursive _ = False
