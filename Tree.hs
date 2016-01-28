{-# LANGUAGE FlexibleInstances #-}
module Tree where
import PGF hiding (showType)
import PGF.Internal hiding (showType)
import Data.Maybe
import Data.List
import Data.Ord
import Grammar
import Debug.Trace

class TreeC t where
  showTree :: t -> String
  selectNode :: t -> Path -> Maybe t
  selectBranch :: t -> Int -> Maybe t

type Cost = Int
type Pos = Int
type Path = [Pos]

type GFAbsTree = Tree

-- A generic tree with types
data TTree = TNode CId FunType [TTree]
           | TMeta CId

data MetaTTree = MetaTTree {
  metaTree :: TTree,
  subTrees :: [(Path,TTree)]
  }
                

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

instance Show TTree where
  show (TNode name typ []) = "{"++ (show name) ++ ":"  ++ show typ ++ "}";
  show (TNode name typ children) = "{" ++ (show name) ++ ":" ++ show typ ++ " " ++ ( unwords $ map show children ) ++ "}"
  show (TMeta cat) = "{?" ++ show cat ++ "}"

-- skipChar :: Char -> String -> String
-- skipChar _ [] = []
-- skipChar c str@(c1:rest)
--   | c == c1 = rest
--   | otherwise = str
-- readId :: String -> (CId,String)
-- readId str =
--     head $ readsPrec 0 str

-- readFunType :: String -> (FunType,String)
-- readFunType str =
--   head $ readsPrec 0 str
-- {t:A -> B -> A {a:A} {g:B -> C -> B {b:B} {c:C}}}
-- A generic tree with types is in the Read class
-- instance Read TTree where
--   readsPrec _ sTree =
--      let
--        combine :: (a,b) -> (a -> c -> a) -> c -> (a,b)
--        combine (a,b) f aa = (f a aa, b)
--        readTrees :: String -> ([TTree],String)
--        readTrees [] = ([],"")
--        readTrees str =
--          let
--            (parse,rest) = trace str $ readTree $ skipChar ' ' str
--          in
--            if str /= rest then combine (readTrees rest) (++) [parse]
--            else ([parse],rest)
--        readTree :: String -> (TTree,String)
--        readTree str =
--          let
--            (id,str2) = readId $ skipChar '{' str
--            (ftype,str3) = trace ( show id ) $ readFunType $ skipChar ':' str2
--            (trees,str4) = trace ( show ftype) $ readTrees str3
--          in
--            ((TNode id ftype trees),skipChar '}' str4)
--      in
--        --fst $ readTree sTree
--        [readTree sTree]
       
instance Eq TTree where
  (==) (TMeta id1) (TMeta id2) = id1 == id2
  (==) (TNode _ typ1 trees1) (TNode _ typ2 trees2) = (typ1 == typ2) && (trees1 == trees2)
  (==) _ _ = False
             
instance Show MetaTTree where
  show tree =
    "(" ++ show (metaTree tree) ++ 
    ", [" ++ unwords (map show (subTrees tree)) ++ "])\n"

instance Eq MetaTTree where
  (==) t1 t2 =
      (metaTree t1 == metaTree t2) && (subTrees t1 == subTrees t2)


-- general helpers
-- replace an element in a list if the position exists
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

maxDepth :: TTree -> Int
maxDepth (TMeta _) = 1
maxDepth (TNode _ _ []) = 1
maxDepth (TNode _ _ trees) =
  1 + (maximum $ map maxDepth trees)


countNodes :: TTree -> Int
countNodes (TNode _ _ trees) = foldl (+) 1 (map countNodes trees)
countNodes (TMeta _) = 0
-- Create a meta tree by appending an empty subtree list
makeMeta :: TTree -> MetaTTree
makeMeta tree =
    MetaTTree tree []

-- replace a branch in a tree by a new tree if a subtree at the position exists
replaceBranch :: TTree -> Pos -> TTree  -> TTree
replaceBranch (TNode id typ trees) pos newTree =
  let
    newSubtrees = listReplace trees pos newTree
  in
    (TNode id typ newSubtrees)
replaceBranch tree _ _ = t

-- replace a subtree given by path by a new tree
replaceNode :: TTree -> Path -> TTree -> TTree
replaceNode oldTree@(TNode _ _ trees) path@(pos:ps) newTree
  | pos < length trees = 
    let
      branch = fromJust $ selectBranch oldTree pos
    in
      replaceBranch oldTree pos (replaceNode branch ps newTree)
  | otherwise = oldTree -- if branch does not exist just do nothing
replaceNode oldTree [] newTree =
  newTree -- at the end of the path just give the new tree to be inserted

-- Replace a node given by a path with a meta
replaceNodeByMeta :: MetaTTree -> Path -> MetaTTree
replaceNodeByMeta tree@(MetaTTree oldMetaTree oldSubTrees) path = 
  let
    newSubTree = fromJust $ selectNode (oldMetaTree) path
    cat = getTreeCat $ newSubTree
    newTree = replaceNode (oldMetaTree) path (TMeta cat)
  in
    MetaTTree newTree ((path,newSubTree):oldSubTrees)

-- Find the maximum length paths not ending in metas
maxPath :: Int -> TTree -> [Path]
maxPath 0 _ = [[]]
maxPath _ (TNode _ _ []) = [[]]
maxPath maxDepth (TNode _ _ trees) =
    let
        branches :: [(Pos, TTree)] -- List of branch positions and subtrees 
        branches = (zip [0..(length trees)] trees)
        relevantBranches :: [(Pos, TTree)] -- List of all branches that don't end in a meta
        relevantBranches = (filter (\t -> case t of { (_, (TNode _ _ _)) -> True ; _ -> False } ) branches)
        relevantPaths :: [(Pos, [Path])] -- List of the maximum pathes of the subtrees for each branch
        relevantPaths = map (\(p,t) -> (p,(maxPath (maxDepth - 1) t))) relevantBranches
        nPaths :: [Path]
        nPaths = concat $ map (\(p,ps) -> map (\s -> p:s) ps ) relevantPaths
        mDepth :: Int
        mDepth = maximum $ 0:(map length nPaths)
        filtered :: [Path]
        filtered = filter (\x -> (length x) == mDepth) nPaths
    in
      case filtered of {
        [] -> [[]] ;
        _ -> filtered
      }
maxPath _ (TMeta _) = [[]]

-- Finds all paths to leaves that are no metas
findPaths :: Int -> TTree -> [Path]
findPaths 0 _ = [[]]
findPaths _ (TNode _ _ []) = [[]]
findPaths maxDepth (TNode _ _ trees) =
    let
        branches :: [(Pos, TTree)] -- List of branch positions and subtrees 
        branches = (zip [0..(length trees)] trees)
        relevantBranches :: [(Pos, TTree)] -- List of all branches that don't end in a meta
        relevantBranches = (filter (\t -> case t of { (_, (TNode _ _ _)) -> True ; _ -> False } ) branches)
        relevantPaths :: [(Pos, [Path])] -- List of the maximum pathes of the subtrees for each branch
        relevantPaths = map (\(p,t) -> (p,(findPaths (maxDepth - 1) t)))  relevantBranches
        paths :: [Path]
        paths = concat $ map (\(p,ps) -> map (\s -> p:s) ps ) relevantPaths
    in
      case paths of {
        [] -> [[]] ;
        _ -> paths
      }
findPaths _ (TMeta _) = [[]]

-- Prune all subtrees to a certain depth
prune :: TTree -> Int -> [MetaTTree]
prune tree depth =
  let
    -- Prunes on multiple nodes
    multiplePrune :: MetaTTree -> [Path] -> MetaTTree
    multiplePrune tree [] = tree
    multiplePrune tree (p:ps) =
      multiplePrune (replaceNodeByMeta tree p) ps
    -- works through a list of trees
    pruneTrees :: MetaTTree -> [MetaTTree] -> Int -> [MetaTTree]
    pruneTrees origTree [] _ = []
    pruneTrees origTree trees depth =
      let
        tree = head trees
        paths = findPaths depth (metaTree tree)
      in
        case paths of {
          [[]] -> nub $ [(replaceNodeByMeta origTree [])] ;
          _ -> 
              let
                finishedTree =  multiplePrune origTree paths 
                todoTrees = map (replaceNodeByMeta tree) paths
               in
                 nub $ finishedTree : (pruneTrees origTree (nub $ tail trees ++ todoTrees) depth)
          }
  in
    reverse $ pruneTrees (makeMeta tree) [(makeMeta tree)] depth

-- Generates list of all meta leaves
getMetaLeaves :: TTree -> [CId]
getMetaLeaves (TMeta id) = [id]
getMetaLeaves (TNode _ _ trees) = concat $ map getMetaLeaves trees

-- Generates list of all pathes to metas
getMetaPaths :: TTree -> [(Path,CId)]
getMetaPaths tree =
  let
    withPath :: TTree -> Path -> [(Path,CId)]
    withPath (TMeta id) path = [(path,id)]
    withPath (TNode _ _ trees) path =
      let
        numberedTrees = zip [0..length trees] trees
      in
        concat $ map (\(b,t) -> withPath t (path ++ [b])) numberedTrees
  in
    withPath tree []
    
-- Find all rules in grammar that have a certain category
getRules :: Grammar -> [CId] -> [Rule]
getRules grammar cats =
    let
        rs = rules grammar
    in
      concat $ map (\c -> filter (\(Function _ (Fun fcat _)) -> fcat == c ) rs) cats

-- expands a tree according to a rule and a path
applyRule :: MetaTTree -> Rule -> [Path] -> MetaTTree
applyRule tree@(MetaTTree oldMetaTree oldSubTrees) rule@(Function name ftype@(Fun cat cats)) (path:pathes) = -- tree --TODO
  let
    newMetaSubTree = (TNode name ftype (map (TMeta) cats)) -- Tree from the rule
    newSubTrees = map (\(subPath,id) -> (path ++ subPath, (TMeta id))) (getMetaPaths newMetaSubTree)
    newTree = (replaceNode (metaTree tree) path newMetaSubTree) -- Get new tree by replacing a meta given by path with the new rule
   in
    applyRule (MetaTTree newTree (oldSubTrees ++ newSubTrees)) rule pathes
applyRule tree rule [] = tree

-- Apply a rule to a meta tree generating all possible new meta trees
combine :: MetaTTree -> Rule -> [MetaTTree]
combine tree@(MetaTTree oldMetaTree oldSubTrees) rule =
  let
    ruleCat = getRuleCat rule
    filteredMetas = filter (\(p,c) -> ruleCat == c) $ getMetaPaths (metaTree tree)
    pathesLists = powerList $ map fst filteredMetas
  in
    map (\pathes ->
          let
            (MetaTTree newMetaTree intermSubTrees) = applyRule tree rule pathes
            newSubTrees = nub $ filter (\(p,_) -> let st = selectNode newMetaTree p in (isJust st) && (isMeta $ fromJust st)) (intermSubTrees ++ oldSubTrees) -- do some filtering to remove all subtrees that are now replaced by the new rules
          in
            (MetaTTree newMetaTree newSubTrees)
        ) pathesLists
    

-- Extend a tree by applying all possible rules once
extendTree :: Grammar -> MetaTTree -> [MetaTTree]
extendTree grammar tree =
  let
      mTree :: TTree
      mTree = metaTree tree
      sTrees :: [(Path,TTree)]
      sTrees = subTrees tree
      metaLeaves :: [CId]
      metaLeaves = nub $ getMetaLeaves mTree
      rules :: [Rule]
      rules = getRules grammar metaLeaves
  in
    nub $ concat $ map (combine tree) rules

generate :: Grammar -> CId -> Int -> [MetaTTree]
generate grammar cat depth =
    let
        loop :: Int -> [MetaTTree] -> [MetaTTree]
        loop 0 oldTrees = oldTrees
        loop count oldTrees =
           let
               newTrees = filter (\t -> maxDepth (metaTree t) <= depth) $ (concat $ map (extendTree grammar) oldTrees)
           in
             oldTrees ++ (loop (count - 1) newTrees)
        startTree = MetaTTree (TMeta cat) [([],(TMeta cat))]
    in
      nub $ loop depth [startTree]

computeCosts :: (TTree,TTree,[TTree],[TTree]) -> Cost
computeCosts (gTree,pTree,_,deleted) =
  foldl (+) (countNodes gTree + countNodes pTree) (map countNodes deleted)

combineTrees :: (TTree,TTree,[TTree],[TTree]) -> TTree
combineTrees (gTree,_,subTrees,_) =
  let
    combineTree :: TTree -> [TTree] -> TTree
    combineTree tree [] = tree
    combineTree tree (subTree:_) =

      let
        paths = map fst $ filter (\(_,cat) -> cat == (getTreeCat subTree)) $ getMetaPaths tree
      in
        -- Here be dragons -> what happens with multiple paths
        replaceNode tree (head paths) subTree
  in
    combineTree gTree subTrees 
match :: MetaTTree -> MetaTTree -> [(Cost, TTree)]
match prunedTree@(MetaTTree pMetaTree pSubTrees) generatedTree@(MetaTTree gMetaTree gSubTrees) =
  let
    replaceCats :: [CId] 
    replaceCats = map (\(_,(TMeta cat)) -> cat) gSubTrees
    replaceSubTrees :: [(Path,TTree)]
    replaceSubTrees = filter (\(_,t) -> isInfixOf [getTreeCat t] replaceCats) pSubTrees
    combinations :: [[(Path,TTree)]]
    combinations = powerList replaceSubTrees
    extractTrees :: [(Path,TTree)] -> [TTree]
    extractTrees trees =
      map (\(_,t) -> t) trees
    magicQuadruple :: [(TTree,TTree,[TTree],[TTree])]
    magicQuadruple = map (\replaceTrees -> let deletedTrees = (extractTrees pSubTrees \\ extractTrees replaceTrees) in (gMetaTree,pMetaTree,extractTrees replaceTrees,deletedTrees)) combinations
    newTrees :: [TTree]
    newTrees = map combineTrees magicQuadruple
    costs :: [Cost]
    costs = map computeCosts magicQuadruple
  in
    sortBy (\(c1,_) (c2,_) -> compare c1 c2) $ zip costs newTrees

t = (TNode (mkCId "t") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TNode (mkCId "a") (Fun (mkCId "A") []) []),(TNode (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")]) [(TNode (mkCId "b") (Fun (mkCId "B") []) []),(TNode (mkCId "c") (Fun (mkCId "C") []) [])])])

t2 = (TNode (mkCId "t2") (Fun (mkCId "F") [(mkCId "A"), (mkCId "G")]) [(TMeta (mkCId "A")), (TNode (mkCId "g") (Fun (mkCId "G") [(mkCId "B"), (mkCId "H")]) [(TMeta (mkCId "B")), (TNode (mkCId "h") (Fun (mkCId "H") [(mkCId "C"), (mkCId "I")]) [(TMeta (mkCId "C")), (TNode (mkCId "i") (Fun (mkCId "I") [(mkCId "D"),(mkCId "E")]) [(TMeta (mkCId "D")), (TMeta (mkCId "E"))])])])])

t3 = let (MetaTTree (TNode _ typ trees) subTrees) = replaceNodeByMeta (replaceNodeByMeta (makeMeta t) [1,0]) [1,1] in (MetaTTree (TNode (mkCId "t3") typ trees) subTrees)

t4 = (TNode (mkCId "t4") (Fun (mkCId "A") [(mkCId "A"),(mkCId "A")]) [(TMeta (mkCId "A")), (TMeta (mkCId "A"))])

g1 = Grammar (mkCId "A")
     [
      Function (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]),
      Function (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")]),
      Function (mkCId "a") (Fun (mkCId "A") []),
      Function (mkCId "b") (Fun (mkCId "B") []),
      Function (mkCId "c") (Fun (mkCId "C") [])
     ]
g2 = Grammar (mkCId "A")
     [
      Function (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "A")]),
      Function (mkCId "a") (Fun (mkCId "A") []) -- ,
--      Function (mkCId "aa") (Fun (mkCId "A") [(mkCId "A")])
     ]

r1 = Function (mkCId "b") (Fun (mkCId "B") [])

r2 = Function (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")])

r3 = Function (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "A")])

--main =
--    generate g1 (mkCId "A") 2


mt11 =
  (MetaTTree
   (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"), (mkCId "B")])
    [
       (TMeta (mkCId "A")),
       (TMeta (mkCId "B"))
    ]
   )
   ([([0], (TNode (mkCId "a") (Fun (mkCId "A") []) [])),
     ([1], (TNode (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")])
            [
              (TNode (mkCId "b") (Fun (mkCId "B") []) []),
              (TNode (mkCId "c") (Fun (mkCId "C") []) [])
            ]
           )
     )
    ]
   )
  )
mt12 =
  (MetaTTree
   (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
    [
      (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
       [
         (TMeta (mkCId "A")),
         (TMeta (mkCId "B"))
       ]
      ),
      (TNode (mkCId "b") (Fun (mkCId "B") []) [])
    ]
   )
   [([0,0], (TMeta (mkCId "A"))),
    ([0,1], (TMeta (mkCId "B")))
   ]
  )
rt1 =
  (4,
   (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
    [
      (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
       [
         (TNode (mkCId "a") (Fun (mkCId "A") []) []),
         (TNode (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")])
          [
            (TNode (mkCId "b") (Fun (mkCId "B") []) []),
            (TNode (mkCId "c") (Fun (mkCId "C") []) [])
          ]
         )
       ]),
      (TNode (mkCId "b") (Fun (mkCId "B") []) [])
    ]
   )
  )
-- (the cost 1 is because the splitted_tree has 1 node, and 3 is because the generated_tree has 3 nodes)
-- Not working yet
mt21 =
  (MetaTTree
   (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"), (mkCId "B")])
    [
      (TMeta (mkCId "A")),
      (TMeta (mkCId "B"))
    ]
   )
   [
     ([0], (TNode (mkCId "a") (Fun (mkCId "A") []) [])),
     ([1], (TNode (mkCId "g") (Fun (mkCId "B") [(mkCId "B"), (mkCId "C")])
            [
              (TNode (mkCId "b") (Fun (mkCId "B") []) []),
              (TNode (mkCId "c") (Fun (mkCId "C") []) [])
            ]
           )
     )
   ]
  )
mt22 =
  (MetaTTree
   (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"), (mkCId "B")])
    [
      (TMeta (mkCId "A")),
      (TNode (mkCId "b") (Fun (mkCId "B") []) [])
    ]
   )
   [
     ([0], (TMeta (mkCId "A")))
   ]
  )
rt2 =
  (6,
   (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"), (mkCId "B")])
    [
      (TNode (mkCId "a") (Fun (mkCId "A") []) []),
      (TNode (mkCId "b") (Fun (mkCId "B") []) [])
    ]
   )
  )
-- (the cost 1 is because the splitted_tree has 1 node, and 2 is because the generated_tree has 2 nodes; the cost 3 is because the B tree was removed, and it has 3 nodes)
