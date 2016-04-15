{-# LANGUAGE FlexibleInstances #-}
module Tree where
import PGF hiding (showType)
import PGF.Internal hiding (showType)
import Data.Maybe
import Data.List
import Data.Set (Set,toList,fromList,empty)
import qualified Data.Set as Set
import Data.Ord
import Grammar
import Debug.Trace

-- Generic class for trees
class TreeC t where
  showTree :: t -> String
  selectNode :: t -> Path -> Maybe t
  selectBranch :: t -> Int -> Maybe t

-- Cost for matching two meta trees
type Cost = Int

-- Position in a path
type Pos = Int

-- Path in a tree
type Path = [Pos]

-- Rename GF abstract syntax tree (from PGF)
type GFAbsTree = Tree

-- A generic tree with types
data TTree = TNode CId FunType [TTree] -- Regular node consisting of a function name, function type and possible subtrees
           | TMeta CId -- A meta tree consisting just of a category type

-- A meta tree - tuple of a generic tree with types and a list of possibly attachable subtrees
data MetaTTree = MetaTTree {
  -- A TTree that can contain meta nodes
  metaTree :: TTree,
  -- List of subtrees that can be attached to the meta nodes determinded by the associated path
  subTrees :: Set (Path,TTree)
  }

-- A GF abstract syntax tree is in TreeC class
instance TreeC GFAbsTree where
  showTree = show
  selectNode t [p] =
    selectBranch t p
  selectNode t (p:ps) =
    let
      branch = selectBranch t p
    in
      case branch of {
        Just b -> selectNode b ps ;
        Nothing -> Nothing
        }
  -- Only branch at applications
  selectBranch (EApp t1 t2) 0 = Just t1
  selectBranch (EApp t1 t2) 1 = Just t2
  selectBranch _ _ = Nothing
  

-- A generic tree with types is in TreeC class
instance TreeC TTree where
  showTree = show
  selectNode t [] = Just t
  selectNode t [b] = selectBranch t b
  selectNode t (hd:tl) =
    let
        branch = (selectBranch t hd)
    in
      case branch of {
        Just b -> selectNode b tl ;
        Nothing -> Nothing
      }
  selectBranch (TMeta _) _ = Nothing
  selectBranch (TNode _ _ [] ) _ = Nothing
  selectBranch (TNode _ _ trees) i = Just (trees !! i)

-- A generic tree with types is in the Show class
instance Show TTree where
  show (TNode name typ []) = "{"++ (show name) ++ ":"  ++ show typ ++ "}";
  show (TNode name typ children) = "{" ++ (show name) ++ ":" ++ show typ ++ " " ++ ( unwords $ map show children ) ++ "}"
  show (TMeta cat) = "{?" ++ show cat ++ "}"

-- Removes a given char at the start of a string if it matches
consumeChar :: Char -> String -> String
consumeChar _ [] = []
consumeChar c str@(c1:rest)
   | c == c1 = rest
   | otherwise = str

-- Read wrapper for a function type that returns just the first parse
readFunType :: String -> Maybe (FunType,String)
readFunType str =
  let
    result = readsPrec 0 str
  in
    if result == [] then Nothing else Just $ head $ result

-- Extracts the root category of each childtree
getChildCats :: TTree -> [CId]
getChildCats (TMeta _) = []
getChildCats (TNode _ _ trees) =
  let
    extract :: TTree -> CId
    extract (TMeta cat) = cat
    extract (TNode _ NoType _) = mkCId "?"
    extract (TNode _ (Fun cat _) _) = cat
  in
    map extract trees

-- goes through a tree and fixes type problems when only a root type is given for each subtree
fixTypes :: TTree -> TTree
fixTypes t@(TNode name typ trees) =
  let
    newType = (Fun (case typ of { NoType -> (mkCId "?") ; (Fun cat _) -> cat }) (getChildCats t))
    newTrees = map fixTypes trees
  in
    (TNode name newType newTrees)
fixTypes t = t

-- Read wrapper for a TTree type that returns just the first parse
readTree  :: String -> Maybe (TTree,String)
readTree str =
  let
    result = readsPrec 0 str
  in
    if result == [] then Nothing else Just $ head $ result

-- reads list of multiple trees
readTrees :: String -> ([TTree],String)
readTrees "" = ([],"")
readTrees sTrees =
  let
    maybeTree = readTree $ consumeChar ' ' sTrees
  in
    case maybeTree of {
      Just tree ->
          let
            more = readTrees $ snd tree
          in
            (fst tree:fst more, snd more) ;
         Nothing -> ([],sTrees) -- trace (show sTrees) $ ([],sTrees)
      }

-- A generic tree with types is in the Read class
instance Read TTree where
  readsPrec _ sTree =
    -- Trees start with a {
    case (consumeChar '{' sTree) of
    {
      -- It is a meta
      ('?':cat) -> let ids = (readsPrec 0 cat) in map (\(a,b) -> ((TMeta a),consumeChar '}' b)) ids ;
      -- or something else
      rest ->
        let
          -- read the id
          maybeId = (readId rest)
        in
          case maybeId of {
            Just id ->
                let
                  -- read the type
                  maybeType = readFunType $ consumeChar ':' $ snd id
                in
                  case maybeType of {
                    Just typ ->
                        let
                          -- read the subtrees
                          strees = (consumeChar '{' $ consumeChar ' ' $ snd typ)
                          trees = readTrees strees
                        in
                          [(fixTypes (TNode (fst $ id) (fst typ) (fst trees)),consumeChar '}' (snd trees))] ;
                    -- No type found
                    Nothing -> [] -- trace ((++) "1:" $ show $ snd id) $ []
                  } ;
            -- No id found
            Nothing -> [] --trace ((++) "2:" $ show rest) $ []
          }
    }

-- A generic tree with types is in the Eq class
{-
  Two TTrees are equal when all types and categories are equal.
  Differences in naming of functions are ignored
-}
instance Eq TTree where
  (==) (TMeta id1) (TMeta id2) = id1 == id2
  (==) (TNode _ typ1 trees1) (TNode _ typ2 trees2) = (typ1 == typ2) && (trees1 == trees2)
  (==) _ _ = False

-- A generic tree with types is in the Eq class
{-
  A tree is smaller if it is not as deep, the category is lexicaly smaller and it has less subtrees
-}
instance Ord TTree where
  (<=) t1 t2 = show t1 <= show t2
-- A meta tree is in the Show class
instance Show MetaTTree where
  show tree =
    "(" ++ show (metaTree tree) ++ 
    ", [" ++ unwords (map show $ toList $ subTrees tree) ++ "])\n"

-- A meta tree is in the Eq class
{-
  Two meta trees are equal if both components are equal cmp. Eq TTree
-}
instance Eq MetaTTree where
  (==) t1 t2 =
      (metaTree t1 == metaTree t2) && (subTrees t1 == subTrees t2)

-- A meta tree is in the Ord class
{-
  Two meta trees are equal if both components are equal cmp. Eq TTree
-}
instance Ord MetaTTree where
  (<=) t1 t2 = show t1 <= show t2
                 
-- List-related functions
-- Replace an element in a list if the position exists
listReplace :: [a] -> Pos -> a -> [a]
listReplace list pos elem
  | 0 <= pos && pos < length list = -- pos in list -> replace it
      let
        (pre,_:post) = splitAt pos list
      in
        pre ++ (elem:post)
  | otherwise = list -- Element not in the list -> return the same list instead

-- generates a power set from a list
powerList :: [a] -> [[a]]
powerList [] = [[]]
powerList (x:xs) = powerList xs ++ map (x:) (powerList xs)


-- Tree-related functions
-- predicate if a tree is just a meta node
isMeta :: TTree -> Bool
isMeta (TMeta _) = True
isMeta _ = False

-- Get the root category of a tree
getTreeCat :: TTree -> CId
getTreeCat (TNode id typ _) =
  let
    (Fun cat _) = typ
  in
    cat
getTreeCat (TMeta cat) = cat

-- Creates a generic tree from an abstract syntax tree
gfAbsTreeToTTree :: PGF -> GFAbsTree -> TTree
gfAbsTreeToTTree pgf (EFun f) =
  let
    typ = getFunType pgf f
  in
    TNode f typ []
gfAbsTreeToTTree pgf (EApp e1 e2) =
  let
    (TNode name typ sts) = gfAbsTreeToTTree pgf e1
    st2 = gfAbsTreeToTTree pgf e2
  in
    (TNode name typ (sts ++ [st2]))

-- Creates a GF abstract syntax Tree from a generic tree
ttreeToGFAbsTree :: TTree -> GFAbsTree
ttreeToGFAbsTree (TNode name _ []) = (EFun name)
ttreeToGFAbsTree (TNode name _ ts) =
  let
     nts = map ttreeToGFAbsTree ts
  in
    mkApp name nts

-- Gets the length of the maximum path between root and a leaf (incl. meta nodes) of a tree
maxDepth :: TTree -> Int
maxDepth (TMeta _) = 1
maxDepth (TNode _ _ []) = 1
maxDepth (TNode _ _ trees) =
  1 + (maximum $ map maxDepth trees)

-- Count all non-meta nodes in a tree
countNodes :: TTree -> Int
countNodes (TNode _ _ trees) = foldl (+) 1 (map countNodes trees)
countNodes (TMeta _) = 0 -- ignore metas

-- Create a meta tree by appending an empty subtree list
makeMeta :: TTree -> MetaTTree
makeMeta tree =
    MetaTTree tree empty

-- Replace a branch in a tree by a new tree if a subtree at the position exists
replaceBranch :: TTree -> Pos -> TTree  -> TTree
replaceBranch (TNode id typ trees) pos newTree =
  let
    newSubtrees = listReplace trees pos newTree -- listReplace takes care of out-of-range positions
  in
    (TNode id typ newSubtrees)
replaceBranch tree _ _ = tree

-- replace a subtree given by path by a new tree
replaceNode :: TTree -> Path -> TTree -> TTree
replaceNode oldTree@(TNode _ _ trees) path@(pos:ps) newTree
  | pos < length trees =  -- subtree must exist
    let
      branch = fromJust $ selectBranch oldTree pos
    in
      replaceBranch oldTree pos (replaceNode branch ps newTree)
  | otherwise = oldTree -- if branch does not exist just do nothing
replaceNode oldTree [] newTree =
  newTree -- at the end of the path just give the new tree to be inserted

-- Replace a node given by a path with a meta node of the same category
replaceNodeByMeta :: MetaTTree -> Path -> MetaTTree
replaceNodeByMeta tree@(MetaTTree oldMetaTree oldSubTrees) path = 
  let
    newSubTree = fromJust $ selectNode (oldMetaTree) path
    cat = getTreeCat $ newSubTree
    newTree = replaceNode (oldMetaTree) path (TMeta cat)
  in
    MetaTTree newTree (Set.insert (path,newSubTree) oldSubTrees)

-- Find the maximum length paths not ending in metas and up to a certain threshold
maxPath :: Int -> TTree -> [Path]
maxPath depth tree =
  let
    paths = findPaths depth tree
    maxLen = maximum (map length paths)
  in
    sort $ filter (\path -> length path == maxLen) paths

-- Finds all paths to leaves that are no metas
findPaths :: Int -> TTree -> [Path]
findPaths 0 _ = [[]]
findPaths _ (TNode _ _ []) = [[]]
findPaths _ (TMeta _) = [[]]
findPaths maxDepth (TNode _ _ trees) =
    let
        branches :: [(Pos, TTree)] -- List of branch positions and subtrees 
        branches = (zip [0..(length trees)] trees)
        relevantPaths :: [(Pos, [Path])] -- List of the maximum pathes of the subtrees for each branch that has not a meta as the next child
        relevantPaths = map (\(p,t) -> (p,(findPaths (maxDepth - 1) t)))  (filter (\(_,t) -> case t of { TMeta _ -> False ; _ -> True }) branches)
        paths :: [Path] -- List of trees and pathes where the current positon is appended to the path
        paths = concat $ map (\(p,ps) -> map (\s -> p:s) ps ) relevantPaths
    in
     case paths of {
       [] -> [[]] ; -- Add at least one element to prevent problems
       _ -> paths
     }


-- Prune all subtrees to a certain depth
prune :: TTree -> Int -> Set MetaTTree
prune tree depth =
  let
    -- Prunes on multiple nodes
    multiplePrune :: MetaTTree -> [Path] -> MetaTTree
    multiplePrune tree [] = tree
    multiplePrune tree (p:ps) =
      multiplePrune (replaceNodeByMeta tree p) ps
    -- Works through a list of trees
    pruneTrees :: MetaTTree -> [MetaTTree] -> Int -> Set MetaTTree
    pruneTrees origTree [] _ = empty
    pruneTrees origTree trees depth =
      let
        tree = head trees
        -- Find all possible paths in the first (possibly already pruned tree)
        paths = findPaths depth (metaTree tree)
      in
        case paths of {
          -- No pathes found -> prune at the root
          [[]] -> Set.singleton (replaceNodeByMeta origTree []) ;
          _ ->
              let
                -- generate a new tree by pruning the original (unpruned) tree with all the paths from the pruned trees
                finishedTree =  multiplePrune origTree paths
                -- Also prune the remaining tree to extend the list of unfinished trees
                todoTrees = map (replaceNodeByMeta tree) paths
               in
                 -- Always remove duplicates (algorithm recreates the same trees sometimes), keep the finished tree and continue with the remainig queue of unfinished trees
                 Set.insert finishedTree (pruneTrees origTree (nub $ tail trees ++ todoTrees) depth)
          }
  in
    Set.insert (makeMeta tree) (pruneTrees (makeMeta tree) [(makeMeta tree)] depth)
-- Generates list of all meta leaves
getMetaLeaves :: TTree -> Set CId
getMetaLeaves (TMeta id) = Set.singleton id
getMetaLeaves (TNode _ _ trees) = Set.unions $ map getMetaLeaves trees

-- Generates list of all pathes to metas
getMetaPaths :: TTree -> [(Path,CId)]
getMetaPaths tree =
  let
    withPath :: TTree -> Path -> [(Path,CId)]
    -- On a meta leave return the id and the path to it
    withPath (TMeta id) path = [(path,id)]
    withPath (TNode _ _ trees) path =
      let
        numberedTrees = zip [0..length trees] trees
      in
        -- Extend path and continue looking for metas
        -- Map over an empty list returns also an empty list
        concat $ map (\(b,t) -> withPath t (path ++ [b])) numberedTrees
  in
    withPath tree []
    
-- Find all rules in grammar that have a certain category
getRules :: Grammar -> [CId] -> Set Rule
getRules grammar cats =
    let
      rs = rules grammar
    in
      -- Convert rules from GF format to our only one
      fromList $ concat $ map (\c -> filter (\(Function _ (Fun fcat _)) -> fcat == c ) rs) cats

-- expands a tree according to a rule and a path
applyRule :: MetaTTree -> Rule -> [Path] -> MetaTTree
applyRule tree@(MetaTTree oldMetaTree oldSubTrees) rule@(Function name ftype@(Fun cat cats)) (path:pathes) =
  let
    newMetaSubTree = (TNode name ftype (map (TMeta) cats)) -- Tree converted from the rule
    newSubTrees = fromList $ map (\(subPath,id) -> (path ++ subPath, (TMeta id))) (getMetaPaths newMetaSubTree) -- Convert list of meta categories to list of TMeta-trees and extended paths that can be used in MetaTrees
    newTree = (replaceNode (metaTree tree) path newMetaSubTree) -- Get new tree by replacing a meta given by path with the new rule
   in
    -- Combine to new MetaTTree and continue applying until no more paths exist
    applyRule (MetaTTree newTree (Set.union oldSubTrees newSubTrees)) rule pathes
applyRule tree rule [] = tree

-- Apply a rule to a meta tree generating all possible new meta trees
combine :: MetaTTree -> Int -> Rule -> Set MetaTTree
combine tree@(MetaTTree oldMetaTree oldSubTrees) depth rule =
  let
    ruleCat :: CId
    ruleCat = getRuleCat rule
    -- Find all meta-nodes that match the category of the rule
    filteredMetas :: [(Path,CId)]
    filteredMetas = filter (\(p,c) -> ruleCat == c && length p <= depth - 1) $ getMetaPaths (metaTree tree)
    -- Generate all possible combinations (powerset)
    pathesLists = powerList $ map fst filteredMetas
  in
    fromList $ map (\pathes ->
          let
            -- Apply rule to the pathes and then split up the MetaTTree into the main tree and the subtrees
            (MetaTTree newMetaTree intermSubTrees) = applyRule tree rule pathes
            -- Do some filtering to remove all subtrees that are now replaced by the new rules
            newSubTrees = Set.filter (\(p,_) -> let st = selectNode newMetaTree p in (isJust st) && (isMeta $ fromJust st)) (Set.union intermSubTrees oldSubTrees) 
          in
            -- Recombine to a new tree
            (MetaTTree newMetaTree newSubTrees)
        ) pathesLists
    

-- Extend a tree by applying all possible rules once
extendTree :: Grammar -> MetaTTree -> Int -> Set MetaTTree
extendTree grammar tree depth =
  let
      -- Split up MetaTTree
      mTree :: TTree
      mTree = metaTree tree
      sTrees :: Set (Path,TTree)
      sTrees = subTrees tree
      -- Get all meta-leaves ...
      metaLeaves :: Set CId
      metaLeaves = getMetaLeaves mTree
      -- ... and grammar rules for them
      rules :: Set Rule
      rules = getRules grammar $ toList metaLeaves
  in
    -- Combine tree with the rules
    trace (show rules) $ Set.unions $ toList $ Set.map (combine tree depth) rules

-- Generates a new MetaTTree with given root-category and maximum height
generate :: Grammar -> CId -> Int -> Set MetaTTree
generate grammar cat depth =
--     let
--         loop :: Int -> [MetaTTree] -> [MetaTTree]
--         loop 0 oldTrees = oldTrees
--         loop count oldTrees =
--            let
--              -- Extend all trees in the working list and remove the ones that have a too great height
--                --newTrees = filter (\t -> maxDepth (metaTree t) <= depth) $ (concat $ map (extendTree grammar) oldTrees)
--              newTrees = (concat $ map (extendTree grammar) oldTrees)
--            in
--              -- Continue and count down depth
--              oldTrees ++ (loop (count - 1) newTrees)
--         -- Generate basic tree from startcta
--         startTree = MetaTTree (TMeta cat) $ Set.singleton ([],(TMeta cat))
--     in
--       -- Loop depth times
--       nub $ loop depth [startTree]
  let
    -- Filter all trees that cannot be extended either because they grow too big or have no free meta nodes
    filterTree :: Int -> MetaTTree -> Bool
    filterTree depth tree =
      let
        metaPaths = filter (\(p,c) -> if length p <= depth - 1 then True else False) $ getMetaPaths (metaTree tree)
      in
        if metaPaths == [] then False -- No more metas to replace
        else True
    -- Generate all trees
    loop :: [MetaTTree] -> Set MetaTTree
    loop [] = empty -- no more "active" trees
    loop (tree:trees) = 
      let
        extended = extendTree grammar tree depth -- these are already part of the result
        activeTrees = trees ++ (filter (filterTree depth) $ toList (Set.delete tree extended))
      in
        trace (show activeTrees) $ Set.union (Set.singleton tree) $ Set.union extended (loop activeTrees)
  in
    loop [(MetaTTree (TMeta cat) (Set.singleton ([], (TMeta cat))))]
    
-- Computes the cost for matching trees. It is the sum of nodes in each of the trees plus the sum of the nodes in all deleted trees
computeCosts :: TTree -> TTree -> [TTree] -> Cost
computeCosts generatedTree prunedTree deletedTrees =
  foldl (+) (countNodes generatedTree + countNodes prunedTree) (map countNodes deletedTrees)

-- Combines a tree with a list of subtrees to a new tree
combineTrees :: TTree -> [TTree] -> TTree
combineTrees generatedTree subTrees =
  let
    combineTree :: TTree -> [TTree] -> TTree
    combineTree tree [] = tree
    combineTree tree (subTree:subTrees) =
      let
        -- Get all pathes to compatible meta-leaves
        paths = map fst $ filter (\(_,cat) -> cat == (getTreeCat subTree)) $ getMetaPaths tree
      in
        -- Use the first of the above paths to combine it to a new tree
        -- Here be dragons -> whatshould we do with the other paths multiple paths
        combineTree (replaceNode tree (head paths) subTree) subTrees 
  in
    combineTree generatedTree subTrees

-- Combines a pruned tree with a generated tree and gives all these combinations ordered by cost for matching
match :: MetaTTree -> MetaTTree -> [(Cost, TTree)]
match prunedTree@(MetaTTree pMetaTree pSubTrees) generatedTree@(MetaTTree gMetaTree gSubTrees) =
  let
    -- Get all the meta categories from the generated MetaTTree (more speficically from the subTree part)
    replaceCats :: [CId] 
    replaceCats = map (\(_,(TMeta cat)) -> cat) $ toList gSubTrees
    -- Find the matching subtrees in the pruned tree
    replaceSubTrees :: Set (Path,TTree)
    replaceSubTrees = Set.filter (\(_,t) -> isInfixOf [getTreeCat t] replaceCats) pSubTrees
    -- Get all possible combinations of them
    combinations :: [[(Path,TTree)]]
    combinations = powerList $ toList $ replaceSubTrees
    -- Tiny wrapper to extract the second part of the tuples
    extractTrees :: [(Path,TTree)] -> [TTree]
    extractTrees trees =
      map snd trees
    -- Pack the parameters and results into one tuple - the generated tree, the pruned tree, the trees used to match the tree, and the removed subtrees
    tempResults :: [(TTree,TTree,[TTree],[TTree])]
    tempResults = map (\replaceTrees -> let deletedTrees = (extractTrees (toList pSubTrees) \\ extractTrees replaceTrees) in (gMetaTree,pMetaTree,extractTrees replaceTrees,deletedTrees)) combinations
    -- Combine the new possible trees
    newTrees :: [TTree]
    newTrees = map (\(p1,_,p3,_) -> combineTrees p1 p3) tempResults
    -- Compute the costs for each of these trees
    costs :: [Cost]
    costs = map (\(p1,p2,_,p4) -> computeCosts p1 p2 p4) tempResults
  in
    -- Sort by cost
    sortBy (\(c1,_) (c2,_) -> compare c1 c2) $ zip costs newTrees
