module Muste.Prune where
import qualified Muste.Feat as F
import Muste.Tree
import Muste.Grammar
import Data.List
import Control.Monad

-- Collect all similar trees of a given <basetree>, according to a <grammar>,
-- by first pruning the tree, then generating all similar pruned trees, then putting all pruned branches back in
--  * <maxCutoff> is the max depth of pruned trees (suggestion: ca 2)
--  * <maxSizeDiff> is the max difference in size (nr of nodes) of the similar pruned trees (suggestion: ca 3-5)
--  * the larger values, the more trees will be generated
-- Returns a list of (path, tree, [(cost, tree', pruned, pruned')]):
--  * <path> is the path to the subtree that is replaced
--  * <cost> is the edit distance between <tree> and <tree'>
--  * <tree> is the original subtree (at position <path>)
--  * <tree'> is the new similar subtree (at position <path>)
--  * <pruned> is the original pruned subtree (at position <path>)
--  * <pruned'> is the new similar pruned subtree (at position <path>)
collectSimilarTrees :: Grammar -> (Int, Int) -> TTree -> [(Path, TTree, [(Int, TTree, TTree, TTree)])]
collectSimilarTrees grammar (maxCutoff, maxSizeDiff) basetree =
    do path <- getPathes basetree
       let Just tree = selectNode basetree path
       return (path, tree, similarTreesForSubtree tree)
    where
      similarTreesForSubtree tree@(TNode _ (F.Fun cat _) _) = 
          do (pruned, branches) <- pruneTree maxCutoff tree
             let metas = getMetas pruned
             let size = countNodes pruned
             size' <- [max 0 (size-maxSizeDiff) .. size+maxSizeDiff]
             let nrtrees = F.featCard (feat grammar) cat size'
             i <- [0 .. nrtrees-1]
             let pruned' = F.featIth (feat grammar) cat size' i

             ---- Alternative 1a: the root must change (==> fewer trees)
             guard $ not (sameRoot pruned pruned')
             ---- Alternative 1b: it's ok if two different children change (==> more trees)
             -- guard $ not (exactlyOneChildDiffers pruned pruned')

             ---- Alternative 2a: all branches are put back into the new tree (==> fewer trees)
             guard $ metas == getMetas pruned'
             ---- Alternative 2b: some branches may be removed from the new tree (==> more trees)
             -- guard $ isSubList metas (getMetas pruned')

             tree' <- insertBranches branches pruned'
             return (treeDiff tree tree', tree', pruned, pruned')
    

-- True if two trees have the same root
sameRoot :: TTree -> TTree -> Bool
sameRoot (TNode fun _ _) (TNode fun' _ _) | fun == fun' = True
sameRoot (TMeta cat) (TMeta cat') | cat == cat' = True
sameRoot _ _ = False


-- True if two trees have the same root, and exactly one child differs
exactlyOneChildDiffers :: TTree -> TTree -> Bool
exactlyOneChildDiffers (TNode fun _ children) (TNode fun' _ children')
    | fun == fun' = difftrees children children'
    where difftrees (t:ts) (t':ts') | t == t' = difftrees ts ts'
                                    | otherwise = ts == ts'
          difftrees _ _ = False
exactlyOneChildDiffers _ _ = False


-- Replace all metavariables in a tree with corresponding branches (with the correct type)
--  * one branch cannot replace two metavariables
--  * this is nondeterministic, because the tree might contain two metavars with the same type
insertBranches :: [TTree] -> TTree -> [TTree]
insertBranches branches tree = map fst (ins branches tree)
    where ins [] tree = [(tree, [])]
          ins branches (TMeta cat) = selectBranch cat branches 
          ins branches (TNode fun typ children) = [ (TNode fun typ children', branches') |
                                                    (children', branches') <- inslist branches children ]
          inslist branches [] = [([], branches)]
          inslist branches (t:ts) = [ (t':ts', branches'') |
                                      (t', branches') <- ins branches t,
                                      (ts', branches'') <- inslist branches' ts ]
          selectBranch _ [] = []
          selectBranch cat (tree@(TNode _ (F.Fun cat' _) _) : trees)
              = [ (tree, trees) | cat == cat' ] ++
                [ (tree', tree:trees') | (tree', trees') <- selectBranch cat trees ]


-- Return a sorted list of the categories of all metavariables in a tree
--  * the list might contain duplicates
getMetas :: TTree -> [String]
getMetas tree = Data.List.sort (getMetas' tree)
    where getMetas' (TMeta cat) = [cat]
          getMetas' (TNode _ _ children) = concatMap getMetas' children


-- Check if all elements in C also occur in D (in the same order)
isSubList :: [String] -> [String] -> Bool
isSubList [] _ = True
isSubList _ [] = False
isSubList csub@(c:sub) (d:super) | c == d    = isSubList sub super
                                 | otherwise = isSubList csub super


-- Return all possible pruned trees up to a given depth
--  * a pruned tree consists of a tree with metavariables,
--  * and a list of all the pruned branches (subtrees)
pruneTree :: Int -> TTree -> [(TTree, [TTree])]
pruneTree 0 tree@(TNode _ _ []) = [(tree, [])]
pruneTree 0 tree@(TNode _ (F.Fun cat _) _) = [(TMeta cat, [tree])]
pruneTree n tree@(TNode fun typ@(F.Fun cat _) children) =
    (TMeta cat, [tree]) : [ (TNode fun typ children', branches) | (children', branches) <- pruneChildren children ]
    where pruneChildren [] = [([], [])]
          pruneChildren (c:cs) = [ (c':cs', bs0 ++ bs1) | (c', bs0) <- pruneTree (n-1) c, (cs', bs1) <- pruneChildren cs ]


-- Edit distance between trees
--  * we use the Levenshtein distance between the list of function nodes in each of the trees
treeDiff :: TTree -> TTree -> Int
treeDiff s t = editDistance (getNodes s) (getNodes t)
    where getNodes (TMeta cat) = ["?" ++ cat]
          getNodes (TNode fun _ children) = fun : concatMap getNodes children


-- Levenshtein distance between two lists, taken from https://wiki.haskell.org/Edit_distance
editDistance :: Eq a => [a] -> [a] -> Int
editDistance a b = last (if lab == 0 then mainDiag
                         else if lab > 0 then lowers !! (lab - 1)
                              else {- < 0 -}  uppers !! (-1 - lab))
    where mainDiag = oneDiag a b (head uppers) (-1 : head lowers)
          uppers   = eachDiag a b (mainDiag : uppers) -- upper diagonals
          lowers   = eachDiag b a (mainDiag : lowers) -- lower diagonals
          eachDiag a [] diags = []
          eachDiag a (bch:bs) (lastDiag:diags) = oneDiag a bs nextDiag lastDiag : eachDiag a bs diags
              where nextDiag = head (tail diags)
          oneDiag a b diagAbove diagBelow = thisdiag
              where doDiag [] b nw n w = []
                    doDiag a [] nw n w = []
                    doDiag (ach:as) (bch:bs) nw n w = me : (doDiag as bs me (tail n) (tail w))
                        where me = if ach == bch then nw else 1 + min3 (head w) nw (head n)
                    firstelt = 1 + head diagBelow
                    thisdiag = firstelt : doDiag a b firstelt diagAbove (tail diagBelow)
          lab = length a - length b
          min3 x y z = if x < y then x else min y z
