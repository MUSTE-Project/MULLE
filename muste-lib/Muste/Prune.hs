module Muste.Prune where
import qualified Muste.Feat as F
import Muste.Tree
import Muste.Grammar
import Control.Monad
import Data.List (sort, nub)


type AdjunctionTrees = [(String, [TTree])]

-- Collect all similar trees of a given <basetree>, according to a <grammar>,
-- by first pruning the tree, then generating all similar pruned trees, then putting all pruned branches back in
-- Returns a list of (path, tree, [(cost, tree', pruned, pruned')]):
--  * <path> is the path to the subtree that is replaced
--  * <cost> is the edit distance between <tree> and <tree'>
--  * <tree> is the original subtree (at position <path>)
--  * <tree'> is the new similar subtree (at position <path>)
--  * <pruned> is the original pruned subtree (at position <path>)
--  * <pruned'> is the new similar pruned subtree (at position <path>)
collectSimilarTrees :: Grammar -> AdjunctionTrees -> TTree -> [(Path, TTree, [(Int, TTree, TTree, TTree)])]
collectSimilarTrees grammar adjTrees basetree =
    do path <- getPathes basetree
       let Just tree = selectNode basetree path
       let simtrees = similarTreesForSubtree tree
       let simtrees' = [sim | sim@(cost, t'', _, _) <- simtrees,
                        not $ or [ cost' < cost && treeDiff t' t'' < cost | (cost', t', _, _) <- simtrees ]]
       return (path, tree, simtrees')
    where
      similarTreesForSubtree :: TTree -> [(Int, TTree, TTree, TTree)]
      similarTreesForSubtree tree@(TNode _ (F.Fun cat _) _) = 
          do let Just adjTreesForCat = lookup cat adjTrees
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
             return (treeDiff tree tree', tree', pruned, pruned')

-- Returns an ordered list with all functions in a tree
getFunctions :: TTree -> [F.Rule]
getFunctions tree = sort (getF tree)
    where getF (TNode fun typ children) = F.Function fun typ : concatMap getF children
          getF _ = []

-- True if the (ordered) list contains no duplicates (i.e., is a set)
noDuplicates :: Eq a => [a] -> Bool
noDuplicates (x:y:zs) | x == y = False
noDuplicates (_:zs) = noDuplicates zs
noDuplicates _ = True

-- True if the (ordered) list (without duplicated) are disjoint
areDisjoint :: Ord a => [a] -> [a] -> Bool
areDisjoint xs@(x:xs') ys@(y:ys')
    | x == y = False
    | x < y = areDisjoint xs' ys
    | otherwise = areDisjoint xs ys'
areDisjoint _ _ = True

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
getMetas tree = sort (getMetas' tree)
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
-- pruneTree :: Int -> TTree -> [(TTree, [TTree])]
-- pruneTree 0 tree@(TNode _ _ []) = [(tree, [])]
-- pruneTree 0 tree@(TNode _ (F.Fun cat _) _) = [(TMeta cat, [tree])]
-- pruneTree n tree@(TNode fun typ@(F.Fun cat _) children) =
--     (TMeta cat, [tree]) : [ (TNode fun typ children', branches) | (children', branches) <- pruneChildren children ]
--     where pruneChildren [] = [([], [])]
--           pruneChildren (c:cs) = [ (c':cs', bs0 ++ bs1) | (c', bs0) <- pruneTree (n-1) c, (cs', bs1) <- pruneChildren cs ]

pruneTree tree = [(t, bs) | (t, bs, _) <- pt [] tree]
    where pt visited tree@(TNode _ _ []) = [(tree, [], visited)]
          pt visited tree@(TNode fun typ@(F.Fun cat _) children)
              = (TMeta cat, [tree], visited) :
                [ (tree', branches', visited') |
                  cat `notElem` visited,
                  (children', branches', visited') <- pc (cat:visited) children,
                  let tree' = TNode fun typ children',
                  True -- not $ treeIsRecursive tree'
                ]
          pc visited [] = [([], [], visited)]
          pc visited (t:ts) = [ (t':ts', bs' ++ bs'', visited'') |
                                (t', bs', visited') <- pt visited t,
                                (ts', bs'', visited'') <- pc visited ts ]

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


getAdjunctionTrees :: Grammar -> AdjunctionTrees
getAdjunctionTrees grammar = [(cat, map fst (adjTrees cat [])) | cat <- allCats]
    where allRules :: [F.Rule]
          allRules = F.getAllRules grammar
          allCats :: [String]
          allCats = nub [cat | (F.Function _ (F.Fun cat _)) <- allRules]
          getRulesFor :: String -> [F.Rule]
          getRulesFor cat = [rule | rule@(F.Function _ (F.Fun cat' _)) <- allRules, cat == cat']
          adjTrees :: String -> [String] -> [(TTree, [String])]
          adjTrees cat visited = (TMeta cat, visited) :
                                 [ (TNode fun typ children, visited') |
                                   cat `notElem` visited,
                                   (F.Function fun typ@(F.Fun _ childcats)) <- getRulesFor cat,
                                   (children, visited') <- adjChildren childcats (cat:visited)
                                 ]
          adjChildren :: [String] -> [String] -> [([TTree], [String])]
          adjChildren [] visited = [([], visited)]
          adjChildren (cat:cats) visited = [ (tree:trees, visited'') |
                                             (tree, visited') <- adjTrees cat visited,
                                             not $ treeIsRecursive tree,
                                             (trees, visited'') <- adjChildren cats visited' ]

treeIsRecursive :: TTree -> Bool
treeIsRecursive tree@(TNode _ (F.Fun cat _) children) =
    case getMetas tree of
      [] -> cat `elem` [cat' | F.Function _ (F.Fun cat' _) <- concatMap getFunctions children]
      [cat'] -> cat == cat'
      _ -> False
treeIsRecursive _ = False

-- -- | Type 'FunType' consists of a String that is the the result category and [String] are the parameter categories
-- data FunType = Fun String [String] | NoType deriving (Ord,Eq,Show,Read)

-- -- | Type 'Rule' consists of a String as the function name and a 'FunType' as the Type
-- data Rule = Function String FunType deriving (Ord,Eq,Show,Read)

-- -- | Type 'Grammar' consists of a start categorie and a list of rules
-- data Grammar = Grammar {
--   startcat :: String,
--   synrules :: [Rule],
--   lexrules :: [Rule],
--   pgf :: PGF,
--   feat :: FEAT
--   }

-- -- | The function 'getRules' returns the union of syntactic and lexical rules of a grammar
-- getAllRules :: Grammar -> [Rule]
-- getAllRules g = union (synrules g) (lexrules g)

-- -- | A generic tree with types
-- data TTree = TNode String FunType [TTree] -- Regular node consisting of a function name, function type and possible subtrees
--            | TMeta String -- A meta tree consisting just of a category type
--            deriving (Ord,Eq,Show,Read) -- read is broken at the moment, most likely because of the CId
