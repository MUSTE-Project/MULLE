{-# Language
    GeneralizedNewtypeDeriving
  , TypeFamilies
#-}
-- FIXME Should this be an internal module? It's not currently used in
-- @muste-ajax@.
module Muste.Prune
  ( AdjunctionTrees
  , getAdjunctionTrees
  , replaceTrees
  ) where

import Control.Monad
import Data.List (sort, nub)
import qualified Data.Containers      as Mono
import Data.MonoTraversable
import qualified Data.Map.Strict      as M
import Data.Maybe

import Muste.Common
import Muste.Tree
import Muste.Grammar


-- * Adjunction trees
--
-- Interfacint with 'AdjunctionTrees' is done using the interface for
-- monomorphic map containers.

-- | @AdjunctionTrees@ really is a map from a @Category@ to a set of
-- trees that have this category.
newtype AdjunctionTrees
  = AdjunctionTrees (M.Map Category [TTree])
  deriving (MonoFunctor)

type instance Element AdjunctionTrees = [TTree]

instance MonoFoldable AdjunctionTrees where
  ofoldl'    f a (AdjunctionTrees m) = ofoldl' f a m
  ofoldr     f a (AdjunctionTrees m) = ofoldr f a m
  ofoldMap   f (AdjunctionTrees m)   = ofoldMap f m
  ofoldr1Ex  f (AdjunctionTrees m)   = ofoldr1Ex f m
  ofoldl1Ex' f (AdjunctionTrees m)   = ofoldl1Ex' f m

instance MonoTraversable AdjunctionTrees where
  otraverse f (AdjunctionTrees m) = AdjunctionTrees <$> otraverse f m

instance Semigroup AdjunctionTrees where
  AdjunctionTrees a <> AdjunctionTrees b = AdjunctionTrees $ a <> b

instance Monoid AdjunctionTrees where
  mempty = AdjunctionTrees mempty

instance GrowingAppend AdjunctionTrees where

instance Mono.SetContainer AdjunctionTrees where
  type ContainerKey AdjunctionTrees = Category
  member k     (AdjunctionTrees m) = Mono.member k m
  notMember k  (AdjunctionTrees m) = Mono.notMember k m
  union        (AdjunctionTrees a) (AdjunctionTrees b) = AdjunctionTrees $ a `Mono.union` b
  intersection (AdjunctionTrees a) (AdjunctionTrees b) = AdjunctionTrees $ a `Mono.intersection` b
  difference   (AdjunctionTrees a) (AdjunctionTrees b) = AdjunctionTrees $ a `Mono.difference` b
  keys         (AdjunctionTrees m) = Mono.keys m

instance Mono.IsMap AdjunctionTrees where
  type MapValue AdjunctionTrees = [TTree]
  lookup c       (AdjunctionTrees m) = Mono.lookup c m
  singletonMap c t                   = AdjunctionTrees $ Mono.singletonMap c t
  mapFromList as                     = AdjunctionTrees $ Mono.mapFromList as
  insertMap k vs (AdjunctionTrees m) = AdjunctionTrees $ Mono.insertMap k vs m
  deleteMap k    (AdjunctionTrees m) = AdjunctionTrees $ Mono.deleteMap k m
  mapToList      (AdjunctionTrees m) = Mono.mapToList m


-- * Replacing trees

-- | @'replaceTrees' grammar adjTs tree@ finds all trees similar to
-- @tree@ in @adjTrees@.  Return a mapping from 'Path''s to the tree
-- you get when you replace one of the valid trees into that given
-- position along with the "cost" of doing so.
replaceTrees :: Grammar -> AdjunctionTrees -> TTree -> [(Path, [(Int, TTree)])]
replaceTrees grammar precomputed tree = do
  (path, _, trees) <- collectSimilarTrees grammar precomputed tree
  pure (path, replaceTree tree path <$> trees)

-- | @'replaceTree' trees@ returns a list of @(cost, t)@ where
-- @t@ is a new tree arising from the 'SimTree'.
replaceTree :: TTree -> Path -> SimTree -> (Int, TTree)
replaceTree tree path (cost, subtree, _, _) = (cost, replaceNode tree path subtree)

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
type ReplacementTree = (Path, TTree, [SimTree])

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
collectSimilarTrees _grammar adjTrees basetree = go <$> getAllPaths basetree
  where
  go :: Path -> ReplacementTree
  go path = (path, tree, simtrees)
    where
      err = error "Muste.Prune.collectSimilarTrees: Incongruence with 'getAllPaths'"
      tree = fromMaybe err $ selectNode basetree path
      -- Get similar trees.
      simtrees = onlyKeepCheapest $ similarTreesForSubtree tree adjTrees
      -- And then additionally filter some out...

-- FIXME Quadratic in the length of 'simtrees'
-- FIXME Shouldn't the condition that the edge between two nodes is
-- less than or equal to the cost be vacously true?
-- | For each tree ensure that no other tree has a lower cost - or
-- that the edge between them is less than the cost.
onlyKeepCheapest :: [SimTree] -> [SimTree]
onlyKeepCheapest simtrees = do
  sim@(cost, t, _, _) <- simtrees
  guard $ not $ or $ do
    (cost', t', _, _) <- simtrees
    pure $ cost' < cost && t' `treeDiff` t < cost
  pure sim

similarTreesForSubtree
  :: TTree
  -> AdjunctionTrees
  -> [SimTree]
similarTreesForSubtree tree@(TNode _ (Fun cat _) _) adjTrees = do
  let
    err = error $ "Muste.Prune.similarTreesForSubtree: "
      <> "The given category does not exist in the adjunction tree"
    adjTreesForCat = fromMaybe err $ Mono.lookup cat adjTrees
  (pruned, branches) <- pruneTree tree
  let funs = getFunctions pruned
  -- guard $ noDuplicates funs
  let metas = getMetas pruned
  pruned' <- adjTreesForCat
  ---- Alternative 1a: the root must change (==> fewer trees)
  -- guard $ not (sameRoot pruned pruned')
  ---- Alternative 1b: it's ok if two different children change (==> more trees)
  -- guard $ not (exactlyOneChildDiffers pruned pruned')
  ---- Alternative 1c: the pruned trees should not share any functions (==> even fewer trees)
  let funs' = getFunctions pruned'
  -- guard $ noDuplicates funs'
  guard $ funs `areDisjoint` funs'
  ---- Alternative 2a: all branches are put back into the new tree (==> fewer trees)
  guard $ metas == getMetas pruned'
  ---- Alternative 2b: some branches may be removed from the new tree (==> more trees)
  -- guard $ isSubList metas (getMetas pruned')
  tree' <- insertBranches branches pruned'
  return (tree `treeDiff` tree', tree', pruned, pruned')
similarTreesForSubtree _ _
  = error "Prune.collectSimiliarTrees: Non-exhaustive pattern match"

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
          pc visited [] = [([], [], visited)]
          pc visited (t:ts) = [ (t':ts', bs' ++ bs'', visited'') |
                                (t', bs', visited') <- pt visited t,
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

-- | Finds all @AdjunctionTrees@ from a specified 'Grammar'.  That is;
-- a mapping from a @Category@ to all trees in the specified 'Grammar'
-- that have this type.
getAdjunctionTrees :: Grammar -> AdjunctionTrees
getAdjunctionTrees grammar = Mono.mapFromList ((\cat -> (cat, map fst (adjTrees cat []))) <$> allCats)
    where allRules :: [Rule]
          allRules = getAllRules grammar
          allCats :: [String]
          allCats = nub [cat | (Function _ (Fun cat _)) <- allRules]
          getRulesFor :: String -> [Rule]
          getRulesFor cat = [rule | rule@(Function _ (Fun cat' _)) <- allRules, cat == cat']
          adjTrees :: String -> [String] -> [(TTree, [String])]
          adjTrees cat visited = (TMeta cat, visited) :
                                 [ (TNode fun typ children, visited') |
                                   cat `notElem` visited,
                                   (Function fun typ@(Fun _ childcats)) <- getRulesFor cat,
                                   (children, visited') <- adjChildren childcats (cat:visited)
                                 ]
          adjChildren :: [String] -> [String] -> [([TTree], [String])]
          adjChildren [] visited = [([], visited)]
          adjChildren (cat:cats) visited = [ (tree:trees, visited'') |
                                             (tree, visited') <- adjTrees cat visited,
                                             not $ treeIsRecursive tree,
                                             (trees, visited'') <- adjChildren cats visited' ]

treeIsRecursive :: TTree -> Bool
treeIsRecursive tree@(TNode _ (Fun cat _) children) =
    case getMetas tree of
      [] -> cat `elem` [cat' | Function _ (Fun cat' _) <- concatMap getFunctions children]
      [cat'] -> cat == cat'
      _ -> False
treeIsRecursive _ = False
