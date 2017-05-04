{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{- | This Module is the internal implementation behind the module 'Muste.Tree' -}
module Muste.Tree.Internal where
import PGF hiding (showType,checkType,parse)
import PGF.Internal hiding (showType)
import Data.Maybe
import Data.List
import Data.Set (Set,toList,fromList,empty)
import qualified Data.Set as Set
import Data.Either
import Data.Ord
import Muste.Grammar.Internal
import Debug.Trace
import Text.Parsec
import Test.QuickCheck

-- | Generic class for trees
class TreeC t where
  showTree :: t -> String
  -- | The function 'selectNode' returns a subtree at given 'Path' if it exists
  selectNode :: t -> Path -> Maybe t
  -- | The function 'selectNode' returns a subtree at given node if it exists
  selectBranch :: t -> Int -> Maybe t

-- | Cost for matching two meta trees
type Cost = Int

-- | Position in a path
type Pos = Int

-- | Path in a tree
type Path = [Pos]

-- | Rename GF abstract syntax tree (from PGF)
type GFAbsTree = Tree

-- | A generic tree with types
data TTree = TNode CId FunType [TTree] -- Regular node consisting of a function name, function type and possible subtrees
           | TMeta CId -- A meta tree consisting just of a category type
           deriving (Ord,Eq,Show,Read)

-- | A meta tree - tuple of a generic tree with types and a list of possibly attachable subtrees
-- data MetaTTree = MetaTTree {
--   -- A TTree that can contain meta nodes
--   metaTree :: TTree,
--   -- List of subtrees that can be attached to the meta nodes determinded by the associated path
--   subTrees :: Set (Path,TTree)
--   }
--                deriving (Eq,Ord)

-- | A labeled tree - just a template to match labels to paths
data LTree = LNode CId Int [LTree] | LLeaf deriving (Show,Eq)

-- | A GF abstract syntax tree is in TreeC class
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
  

-- | A generic tree with types is in TreeC class
instance TreeC TTree where
  showTree = show
  selectNode t [] = Just t
  selectNode t [b] = selectBranch t b
  selectNode t (hd:tl) =
    let
        branch = selectBranch t hd
    in
      case branch of {
        Just b -> selectNode b tl ;
        Nothing -> Nothing
      }
  selectBranch (TMeta _) _ = Nothing
  selectBranch (TNode _ _ [] ) _ = Nothing
  selectBranch (TNode _ _ trees) i
    | i < 0 || i >= length trees = Nothing
    | otherwise = Just (trees !! i)

arbitraryGFAbsTree :: Grammar -> Int -> Gen GFAbsTree
arbitraryGFAbsTree grammar depth =
  let
    closure :: Grammar -> Int -> GFAbsTree -> Gen GFAbsTree
    closure grammar depth tree = return tree
    -- case 1: only the start symbol => first expansion
    -- case 2: tree that can still be expanded
    -- case 3: complete tree of sufficient depth
      -- | not $ hasMetas tree = return tree
      -- | otherwise = return tree
  in
    do
      let start = startcat grammar
      closure grammar depth (mkApp start [])

--   do
--     let ids = ['a'..'z']
--     id <- elements ids
--     t1 <- arbitrary
--     t2 <- arbitrary
--     frequency [(3,return (EApp t1 t2)),(7,return (EFun $ mkCId [id]))]
  
-- | A GF abstract syntax tree with types is in Arbitrary class
-- instance Arbitrary GFAbsTree where
--   arbitrary =
--     do
--       g <- arbitrary
--       arbitraryGFAbsTree g

arbitraryTTree :: Grammar -> Int -> Gen TTree
arbitraryTTree grammar depth =
  let
    closure :: Grammar -> Int -> TTree -> Gen TTree
    closure grammar depth tree
      | not $ hasMetas tree = return tree
      | otherwise = 
        do
          -- get all metas
          let metas = getMetaPaths tree
          -- get one of the metas
          (path,cat) <- elements metas
          -- get all the rules for the meta category
          let lrules = getRulesList (synrules grammar) [cat]
          let srules = getRulesList (lexrules grammar) [cat]
          -- prefer lexical rules
          rules <- frequency [(8, return lrules), (2, return  srules)]
          -- get one of the rules but handle the case that the preferred category is empty
          -- here be dragons, but why?
          rule <- elements $ if null rules then union lrules srules else rules
          -- apply rule
          let ntree = applyRule tree rule [path]
          -- check tree for validity
          if maxDepth ntree <= depth then closure grammar depth ntree else closure grammar depth tree
  in
    do
      let start = TMeta (startcat grammar)
      closure grammar depth start


-- | A generic tree with types is in Arbitrary class
instance Arbitrary TTree where
  arbitrary =
    do
      g <- arbitrary
      resize 5 $ sized $ arbitraryTTree g -- temporary resize

prop_treeConversionIdentity :: Grammar -> TTree -> Gen Property
prop_treeConversionIdentity g tree =
  let
    compatible grammar (TNode id typ ts) =
      elem (Function id typ) (getAllRules g) && (and $ map (compatible grammar) ts)
  in
    do
      --    tree <- arbitraryTTree g 5
      return $ compatible g tree ==> ((gfAbsTreeToTTree2 g . ttreeToGFAbsTree) tree) == tree

-- | A generic 'TTree' with types is in the 'Show' class
-- instance Show TTree where
--   show (TNode name typ []) = "{"++ show name ++ ":"  ++ show typ ++ "}";
--   show (TNode name typ children) = "{" ++ show name ++ ":" ++ show typ ++ " " ++ unwords ( map show children ) ++ "}"
--   show (TMeta cat) = "{?" ++ show cat ++ "}"

-- | A 'MetaTTree' is in the 'Show' class
-- instance Show MetaTTree where
--   show tree =
--     "(" ++ show (metaTree tree) ++ 
--     ", [" ++ unwords (map show $ toList $ subTrees tree) ++ "])"

-- | The function 'consumeChar' removes a given char at the start of a string if it matches
-- consumeChar :: Char -> String -> String
-- consumeChar _ [] = []
-- consumeChar c str@(c1:rest)
--    | c == c1 = rest
--    | otherwise = str

-- | The function 'readFunType' is a read wrapper for a function type that returns just the first parse
readFunType :: String -> Maybe (FunType,String)
readFunType str =
  let
    result = reads str
  in
    case result of {
      [(NoType,_)] -> Nothing ;
      _ -> Just $ head result
      }

-- | The function 'getChildCats' extracts the root category of each childtree
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

-- | The function 'checkType' typechecks a 'TTree'
checkType :: TTree -> Bool
checkType (TMeta _) = True
checkType t@(TNode name (Fun fcat ccats) trees) =
  (getChildCats t == ccats) && all checkType trees

-- | The function 'fixTypes' goes through a 'TTree' and fixes type problems when only a root type is given for each subtree
fixTypes :: TTree -> TTree
fixTypes t@(TNode name typ trees) =
  let
    newType = case typ of {
      NoType -> Fun (mkCId "?") []; -- No type at all
      (Fun cat []) -> Fun cat (getChildCats t); -- No type info for the subtrees -> Copy categories
      f@(Fun cat _) -> f -- Already typed -> Do nothing
      }
    newTrees = map fixTypes trees
  in
    TNode name newType newTrees
fixTypes t = t

-- parsecTTrees :: Stream s m Char => ParsecT s u m [TTree]
-- parsecTTrees =
--   many1 (trace "TTree" $ parsecTTree)

-- parsecTMeta :: Stream s m Char => ParsecT s u m TTree
-- parsecTMeta =
--   do
--     char '?'
--     id <- many1 $ noneOf "} "
--     return (TMeta $ mkCId id)
    
-- parsecTNode :: Stream s m Char => ParsecT s u m (TTree)
-- parsecTNode =
--   do
--     id <- many1 $ noneOf ":?} "
--     spaces
--     char ':'
--     spaces
--     typ <- trace "FunType" $ parsecFunType
--     spaces
--     trees <- trace "TTrees" $ parsecTTrees
-- --    spaces
--     return (TNode (mkCId id) typ [])

-- parsecTTree :: Stream s m Char => ParsecT s u m TTree
-- parsecTTree =
--   do
--     char '{'
--     -- tree <- (trace "TMeta" $ parsecTMeta) <|> (trace "TNode" $ parsecTNode)
--     tree <- parsecTNode <|> parsecTMeta
--     char '}'
--     spaces
--     return tree
    
-- -- | The function 'readTree' is only a 'Read' wrapper for a 'TTree' type that returns just the first parse
-- readTree  :: String -> Maybe (TTree,String)
-- readTree str =
--   let
--     result = reads str
--   in
--     if null result then Nothing else Just $ head result

-- -- | The function 'readTrees' reads list of multiple 'TTree's
-- readTrees :: String -> ([TTree],String)
-- readTrees "" = ([],"")
-- readTrees sTrees =
--   let
--     maybeTree = readTree $ consumeChar ' ' sTrees
--   in
--     case maybeTree of {
--       Just tree ->
--           let
--             more = readTrees $ snd tree
--           in
--             (fst tree:fst more, snd more) ;
--          Nothing -> ([],sTrees) -- trace (show sTrees) $ ([],sTrees)
--       }

-- | A generic 'TTree' with types is in the 'Read' class
-- instance Read TTree where
--   readsPrec _ sTree =
--     let
--       result = parse (parsecPlusRest parsecTTree) "read" sTree
--     in
--       case result of {
--         Left e -> error $ show e ;
--         Right (fun,rest) -> [(fun,rest)]
--         }
-- -- Old Read
-- --     -- Trees start with a {
-- --     case consumeChar '{' sTree of
-- --     {
-- --       -- It is a meta
-- --       ('?':cat) -> let ids = reads cat in map (\(a,b) -> (TMeta a,consumeChar '}' b)) ids ;
-- --       -- or something else
-- --       rest ->
-- --         let
-- --           -- read the id
-- --           maybeId = readId rest
-- --         in
-- --           case maybeId of {
-- --             Just id ->
-- --                 let
-- --                   -- read the type
-- --                   maybeType = readFunType $ consumeChar ':' $ snd id
-- --                 in
-- --                   case maybeType of {
-- --                     Just typ ->
-- --                         let
-- --                           -- read the subtrees
-- --                           strees = consumeChar '{' $ consumeChar ' ' $ snd typ
-- --                           trees = readTrees strees
-- --                         in
-- --                           [(fixTypes (TNode (fst id) (fst typ) (fst trees)),consumeChar '}' (snd trees))] ;
-- --                     -- No type found
-- --                     Nothing -> [] -- trace ((++) "1:" $ show $ snd id) $ []
-- --                   } ;
-- --             -- No id found
-- --             Nothing -> [] --trace ((++) "2:" $ show rest) $ []
-- --           }
-- --     }
                 
-- List-related functions
-- | The function 'listReplace' replaces an element in a 'List' if the position exists
listReplace :: [a] -> Pos -> a -> [a]
listReplace list pos elem
  | 0 <= pos && pos < length list = -- pos in list -> replace it
      let
        (pre,_:post) = splitAt pos list
      in
        pre ++ (elem:post)
  | otherwise = list -- Element not in the list -> return the same list instead

-- | The function 'powerList' generates a power set from a 'List'
powerList :: [a] -> [[a]]
powerList [] = [[]]
powerList (x:xs) = powerList xs ++ map (x:) (powerList xs)

     
-- Tree-related functions
-- | The funcion 'isMeta' is a predicate that is true if a 'TTree' is just a 'TMeta' node
isMeta :: TTree -> Bool
isMeta (TMeta _) = True
isMeta _ = False

-- | The function 'getTreeCat' gives the root category of a 'TTree', returns 'wildCId' on missing type
getTreeCat :: TTree -> CId
getTreeCat (TNode id typ _) =
  case typ of {
    (Fun cat _) -> cat ;
    NoType -> wildCId
    }
getTreeCat (TMeta cat) = cat

-- | The function 'gfAbsTreeToTTree' creates a 'TTree' from an GFabstract syntax 'Tree'. Handles only 'EApp' and 'EFun'. Generates 'TMeta' 'wildCId' in unsupported cases
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
    TNode name typ (sts ++ [st2])
gfAbsTreeToTTree pgf _ = TMeta wildCId

-- | Creates a GF abstract syntax Tree from a generic tree
ttreeToGFAbsTree :: TTree -> GFAbsTree
ttreeToGFAbsTree tree =
  let
    loop :: [TTree] -> Int -> (Int,[GFAbsTree])
    loop [] id = (id,[])
    loop (t:ts) id =
      let
        (nid,nt) = convert t id
        (fid,nts) = loop ts nid
      in
        (fid,nt:nts)
    convert :: TTree -> Int -> (Int,GFAbsTree)
    convert (TMeta _) id = (id + 1, mkMeta id)
    convert (TNode name _ ns) id =
      let
        (nid,nts) = loop ns id
      in
        (nid,mkApp name nts)
  in
    snd $ convert tree 0

-- | Creates a labeled LTree from a TTree
ttreeToLTree :: TTree -> LTree
ttreeToLTree tree =
  let
    -- Convert structure without caring about labels
    convert (TMeta cat) = LNode cat (-1) [LNode (mkCId "_") (-1) [LLeaf]]
    convert (TNode _ (Fun cat _) []) = LNode cat (-1) []
    convert (TNode _ (Fun cat _) ts) = LNode cat (-1) (map convert ts)
    -- Update the labels in a tree
    update :: Int -> LTree -> (Int, LTree)
    update pos LLeaf = (pos, LLeaf)
    update pos (LNode cat id []) = (pos + 1, LNode cat pos [])
    update pos (LNode cat id ns) =
      let
        (npos,ults) = updates pos ns
      in
        (npos + 1, LNode cat npos ults)
    -- Update a list of trees
    updates :: Int -> [LTree] -> (Int, [LTree])
    updates pos [] = (pos, [])
    updates pos (lt:lts) =
      let
        (npos1,ult) = update pos lt
        (npos,ults) = updates npos1 lts
      in
        (npos, ult:ults)
    
  in
    snd $ update 0 $ convert tree

-- | The function 'showBracketed' shows a bracketed string in a more verbose way than 'showBracketedString' from 'PGF'
showBracket (Bracket cid fid lindex cid2 exprs bs) =
  "[Bracket (cid1:" ++ show cid ++ ") (fid:" ++ show fid ++ ") (lindex:" ++ show lindex ++ ") (cid2:" ++ show cid2 ++ ") (exprs:" ++ show exprs ++ ") (bs:[" ++ unwords ( map showBracket bs) ++ "]) ]"
showBracket (Leaf token) = "[Leaf (token:" ++ token ++ ")]"

-- | The function 'getPath' finds a path to a node with a given label in a labeled tree
getPath :: LTree -> Int -> Path
getPath ltree id = 
  let
    deep :: LTree -> Int -> Path -> Path
    deep LLeaf _ _ = []
--    deep (LNode cid fid []) id path = if fid == id then path else []
    deep (LNode cid fid ns) id path = if fid == id then path else broad ns id path 0
    broad :: [LTree] -> Int -> Path -> Pos -> Path
    broad [] _ _ _ = []
    broad (n:ns) id path pos =
      let
        d = deep n id (pos:path)
        b = broad ns id path (pos + 1)
      in
        if not $ null d then d else b
  in
    reverse $ deep ltree id [] -- getPathWithPos id [] 0 ltree

-- | The function 'maxDepth' gets the length of the maximum path between root and a leaf (incl. meta nodes) of a 'TTree'
maxDepth :: TTree -> Int
maxDepth (TMeta _) = 1
maxDepth (TNode _ _ []) = 1
maxDepth (TNode _ _ trees) =
  1 + maximum ( map maxDepth trees )

-- | The function 'countNodes' count all non-meta nodes in a 'TTree'
countNodes :: TTree -> Int
countNodes (TNode _ _ trees) = foldl (+) 1 (map countNodes trees)
countNodes (TMeta _) = 0 -- ignore metas

-- | Create a meta tree by appending an empty subtree list
-- makeMeta :: TTree -> MetaTTree
-- makeMeta tree =
--     MetaTTree tree empty

-- | The function 'replaceBranch' replaces a branch in a 'TTree' by a new 'TTree' if a subtree at the position exists
replaceBranch :: TTree -> Pos -> TTree  -> TTree
replaceBranch (TNode id typ trees) pos newTree =
  let
    newSubtrees = listReplace trees pos newTree -- listReplace takes care of out-of-range positions
  in
    TNode id typ newSubtrees
replaceBranch tree _ _ = tree

-- | The function 'replaceNode' replaces a subtree given by 'Path' in a 'TTree'
replaceNode :: TTree -> Path -> TTree -> TTree
replaceNode oldTree@(TNode _ _ trees) path@(pos:ps) newTree
  | pos >= 0 && pos < length trees =  -- subtree must exist
    let
      branch = fromJust $ selectBranch oldTree pos
    in
      replaceBranch oldTree pos (replaceNode branch ps newTree)
  | otherwise = oldTree -- if branch does not exist just do nothing
replaceNode oldTree [] newTree =
  newTree -- at the end of the path just give the new tree to be inserted
replaceNode oldTree _ _ =
  oldTree -- No more subtrees, cancel search

-- | The function 'replaceNodeByMeta' replaces a node given by a 'Path' with a meta node of the same category
-- replaceNodeByMeta :: MetaTTree -> Path -> MetaTTree
-- replaceNodeByMeta tree@(MetaTTree oldMetaTree oldSubTrees) path = 
--   let
--     newSubTree = selectNode oldMetaTree path
--     cat = getTreeCat $ fromJust newSubTree -- scary but should work due to lazy evaluation
--     newTree = replaceNode oldMetaTree path (TMeta cat)
--   in
--     case newSubTree of {
--       Just t -> MetaTTree newTree (Set.insert (path,t) oldSubTrees) ;
--       -- invalid path, just return the tree
--       _ -> tree
--       }

-- | The function 'maxPath' finds the maximum length paths not ending in metas and up to a certain threshold
maxPath :: Int -> TTree -> [Path]
maxPath depth tree =
  let
    paths = findLeafPaths depth tree
    maxLen = maximum (map length paths)
  in
    sort $ filter (\path -> length path == maxLen) paths

-- | The function 'findPaths' finds all paths
findPaths :: TTree -> [Path]
findPaths (TMeta _) = []
findPaths (TNode _ _ trees) =
  let
    current = [[n] | n <- [0 .. length trees - 1]]
  in
    current ++ (concat $ map (\(x,xs) -> map (x:) xs) $ zip (concat current) (map findPaths trees))
    
-- | The function 'findLeafPaths' finds all paths to leaves that are no metas
findLeafPaths :: Int -> TTree -> [Path]
findLeafPaths 0 _ = [[]]
findLeafPaths _ (TNode _ _ []) = [[]]
findLeafPaths _ (TMeta _) = [[]]
findLeafPaths maxDepth (TNode _ _ trees) =
    let
        branches :: [(Pos, TTree)] -- List of branch positions and subtrees 
        branches = zip [0..(length trees)] trees
        relevantPaths :: [(Pos, [Path])] -- List of the maximum pathes of the subtrees for each branch that has not a meta as the next child
        relevantPaths = map (\(p,t) -> (p,findLeafPaths (maxDepth - 1) t))  (filter (\(_,t) -> case t of { TMeta _ -> False ; _ -> True }) branches)
        paths :: [Path] -- List of trees and pathes where the current positon is appended to the path
        paths = concatMap (\(p,ps) -> map (\s -> p:s) ps ) relevantPaths
    in
     case paths of {
       [] -> [[]] ; -- Add at least one element to prevent problems
       _ -> paths
     }


-- | The function 'prune' runes a 'TTree' to a certain depth ans stores all removed subtrees 
-- prune :: TTree -> Int -> Set MetaTTree
-- prune tree depth =
--   let
--     -- Prunes on multiple nodes
--     multiplePrune :: MetaTTree -> [Path] -> MetaTTree
--     multiplePrune = foldl replaceNodeByMeta
--     -- Works through a list of trees
--     pruneTrees :: MetaTTree -> [MetaTTree] -> Int -> Set MetaTTree
--     pruneTrees origTree [] _ = empty
--     pruneTrees origTree trees depth =
--       let
--         tree = head trees
--         -- Find all possible paths in the first (possibly already pruned tree)
--         paths = findLeafPaths depth (metaTree tree)
--       in
--         case paths of {
--           -- No pathes found -> prune at the root
--           [[]] -> Set.singleton (replaceNodeByMeta origTree []) ;
--           _ ->
--               let
--                 -- generate a new tree by pruning the original (unpruned) tree with all the paths from the pruned trees
--                 finishedTree =  multiplePrune origTree paths
--                 -- Also prune the remaining tree to extend the list of unfinished trees
--                 todoTrees = map (replaceNodeByMeta tree) paths
--                in
--                  -- Always remove duplicates (algorithm recreates the same trees sometimes), keep the finished tree and continue with the remainig queue of unfinished trees
--                  Set.insert finishedTree (pruneTrees origTree (nub $ tail trees ++ todoTrees) depth)
--           }
--   in
--     Set.insert (makeMeta tree) (pruneTrees (makeMeta tree) [makeMeta tree] depth)

-- | The function 'getMetaLeafCats' returns set of the categories of all meta leaves
getMetaLeafCatsSet :: TTree -> Set CId
getMetaLeafCatsSet (TMeta id) = Set.singleton id
getMetaLeafCatsSet (TNode _ _ trees) = Set.unions $ map getMetaLeafCatsSet trees

-- | The function 'getMetaLeafCats' returns set of the categories of all meta leaves
getMetaLeafCatsList :: TTree -> [CId]
getMetaLeafCatsList (TMeta id) = [id]
getMetaLeafCatsList (TNode _ _ trees) = concat $ map getMetaLeafCatsList trees

-- | The function 'getMetaPaths' generates alist of all pathes to metas
getMetaPaths :: TTree -> [(Path,CId)]
getMetaPaths tree =
  let
    withPath :: TTree -> Path -> [(Path,CId)]
    -- On a meta leaf return the id and the path to it
    withPath (TMeta id) path = [(path,id)]
    withPath (TNode _ _ trees) path =
      let
        numberedTrees = zip [0..length trees] trees
      in
        -- Extend path and continue looking for metas
        -- Map over an empty list returns also an empty list
        concatMap (\(b,t) -> withPath t (path ++ [b])) numberedTrees
  in
    withPath tree []
    
-- | The function 'applyRule' expands a 'TTree' according to a 'Rule' and a 'Path'
applyRule :: TTree -> Rule -> [Path] -> TTree
applyRule tree rule@(Function name ftype@(Fun cat cats)) (path:pathes) =
  let
    newMetaSubTree = TNode name ftype (map TMeta cats) -- Tree converted from the rule
    newTree = replaceNode tree path newMetaSubTree -- Get new tree by replacing a meta given by path with the new rule
   in
    -- Combine to new TTree and continue applying until no more paths exist
    applyRule newTree rule pathes
applyRule tree (Function _ NoType) _ = tree -- No rule type, same tree
applyRule tree rule [] = tree -- No path, same tree

-- | The function 'combine' applies a 'Rule' to a 'TTree' generating all possible new meta trees, the depth parameter limits the search for metas to be replaced
combineSet :: TTree -> Int -> Rule -> Set TTree
combineSet tree depth rule =
  let
    ruleCat :: CId
    ruleCat = getRuleCat rule
    -- Find all meta-nodes that match the category of the rule
    filteredMetas :: [(Path,CId)]
    filteredMetas = filter (\(p,c) -> ruleCat == c && length p <= depth - 1) $ getMetaPaths tree
    -- Generate all possible combinations (powerset)
    pathesLists = powerList $ map fst filteredMetas
  in
    fromList $ map (\pathes ->
          let
            -- Apply rule to the pathes and then split up the TTree into the main tree and the subtrees
            newTree = applyRule tree rule pathes
          in
            newTree
        ) pathesLists

-- | The function 'extendTree' extends a 'TTree' by applying all applicable rules from a 'Grammar' once
extendTree :: Grammar -> TTree -> Int -> Set TTree
extendTree grammar tree depth =
  let
      -- Get all meta-leaves ...
      metaLeaves :: Set CId
      metaLeaves = getMetaLeafCatsSet tree
      -- ... and grammar rules for them
      rules :: Set Rule
      rules = getRulesSet (getAllRules grammar) $ toList metaLeaves
  in
    -- Combine tree with the rules
    Set.unions $ toList $ Set.map (combineSet tree depth) rules

-- | The function 'generate' generates all possible 'TTree's with given root-category up to a maximum height
generateSet :: Grammar -> CId -> Int -> Set TTree
generateSet grammar cat depth =
  let
    -- Filter all trees that cannot be extended either because they grow too big or have no free meta nodes
    filterTree :: Int -> TTree -> Bool
    filterTree depth tree =
      let
        metaPaths = filter (\(p,c) -> length p <= depth - 1) $ getMetaPaths tree
      in
        not $ null metaPaths
    -- Generate all trees
    loop :: [TTree] -> Set TTree
    loop [] = empty -- no more "active" trees
    loop (tree:trees) = 
      let
        extended = extendTree grammar tree depth -- these are already part of the result
        activeTrees = trees ++ filter (filterTree depth) (toList (Set.delete tree extended))
      in
        Set.union (Set.singleton tree) $ Set.union extended (loop activeTrees)
  in
    loop [TMeta cat]

-- | The function 'combine' applies a 'Rule' to a 'TTree' generating all possible new meta trees, the depth parameter limits the search for metas to be replaced
combineList :: TTree -> Int -> Rule -> [TTree]
combineList tree depth rule =
  let
    ruleCat :: CId
    ruleCat = getRuleCat rule
    -- Find all meta-nodes that match the category of the rule
    filteredMetas :: [(Path,CId)]
    filteredMetas = filter (\(p,c) -> ruleCat == c && length p <= depth - 1) $ getMetaPaths tree
    -- Generate all possible combinations (powerset)
    pathesLists = powerList $ map fst filteredMetas
  in
    map (\pathes ->
          let
            -- Apply rule to the pathes and then split up the TTree into the main tree and the subtrees
            newTree = applyRule tree rule pathes
          in
            newTree
        ) pathesLists


-- | The function 'extendTree' extends a 'TTree' by applying all applicable rules from a 'Grammar' once
extendTreeList :: Grammar -> TTree -> Int -> [TTree]
extendTreeList grammar tree depth =
  let
      -- Get all meta-leaves ...
      metaLeaves :: [CId]
      metaLeaves = getMetaLeafCatsList tree
      -- ... and grammar rules for them
      rules :: [Rule]
      rules = getRulesList (getAllRules grammar) metaLeaves
  in
    -- Combine tree with the rules
    concatMap (combineList tree depth) rules

    -- | The function 'generate' generates all possible 'TTree's with given root-category up to a maximum height
generateListSimple :: Grammar -> CId -> Int -> [TTree]
generateListSimple grammar cat depth =
  let
    -- Filter all trees that cannot be extended either because they grow too big or have no free meta nodes
    filterTree :: Int -> TTree -> Bool
    filterTree depth tree =
       let
         metaPaths = filter (\(p,c) -> length p <= depth - 1) $ getMetaPaths tree
       in
         not $ null metaPaths
    -- Generate all trees
    loop :: [TTree] -> [TTree]
    loop [] = [] -- no more "active" trees
    loop trees = 
      let
        extendedTrees = concatMap (\t -> extendTreeList grammar t depth) trees -- these are already part of the result
      in
        trace (show trees) $ nub $ trees ++ loop extendedTrees
  in
    loop [TMeta cat]

generateListPGF :: Grammar -> CId -> Int -> [TTree]
generateListPGF grammar startCat depth =
  let
    trees = generateAllDepth (pgf grammar) (fromJust $ readType $ showCId startCat) (Just depth)
  in
    map (gfAbsTreeToTTree $ pgf grammar) trees
    
-- | The function 'computeCosts' computes the cost for matching trees. It is the sum of nodes in each of the trees plus the sum of the nodes in all deleted trees
computeCosts :: TTree -> TTree -> [TTree] -> Cost
computeCosts generatedTree prunedTree deletedTrees =
  foldl (+) (countNodes generatedTree + countNodes prunedTree) (map countNodes deletedTrees)

combineTrees :: TTree -> [TTree] -> [TTree]
combineTrees generatedTree [] = [generatedTree]
combineTrees generatedTree subTrees =
  let
    translateCategoriesToSubTrees :: [(Path,CId)] -> [TTree] -> [[(Path,TTree)]]
    translateCategoriesToSubTrees [] _ = []
    translateCategoriesToSubTrees _ [] = []
    translateCategoriesToSubTrees ps ts =
      let sts =
            let
              tsts = map (\p -> filter (\t -> snd p == getTreeCat t) ts) ps :: [[TTree]]
              tcts = map (\(_,c) -> length $ filter (\(_,c2) -> c == c2) ps) ps :: [Int]
            in
              ( map (\(t,c) ->
                      if length t < c then
                        if null t then
                          []
                        else
                          t ++ replicate (c - length t) (TMeta $ getTreeCat $ head t)
                      else t)
                $ zip tsts tcts
              ) :: [[TTree]]
          combine :: [(Path,CId)] -> [[TTree]] -> [TTree] -> [[(Path,TTree)]]
          combine [(p,_)] [ts] _ =
            let tmp = map (\t -> [(p,t)]) ts
            in if null tmp then [[]] else tmp -- list shall not be empty at the end
          combine _ ([]:_) _ = trace "c2" [] 
          combine ps@((p,_):rps) ts@(t:rts) used =
            let
              tree = head t
              res = combine rps (map (delete tree) rts) (tree:used) :: [[(Path,TTree)]]
              p1 = map ((p,tree) :) res :: [[(Path,TTree)]]
              p2 = combine ps (tail t:rts) used :: [[(Path,TTree)]]
            in
              p1 ++ p2
      in
        combine ps sts []
    ps = getMetaPaths generatedTree 
    ts = translateCategoriesToSubTrees ps subTrees :: [[(Path,TTree)]]
  in
    if null ps || null ts then
      [generatedTree]
    else
      map (foldl (\tree (path,subTree) -> replaceNode tree path subTree) generatedTree) ts
  
-- | The function 'match' combines a pruned tree with a generated tree and gives all these combinations ordered by cost for matching
-- match :: MetaTTree -> MetaTTree -> [(Cost, TTree)]
-- match prunedTree@(MetaTTree pMetaTree pSubTrees) generatedTree@(MetaTTree gMetaTree gSubTrees) =
--   let
--     -- Get all the meta categories from the generated MetaTTree (more speficically from the subTree part)
--     replaceCats :: [CId] 
--     replaceCats = map (\(_,TMeta cat) -> cat) $ toList gSubTrees
--     -- Find the matching subtrees in the pruned tree
--     replaceSubTrees :: Set (Path,TTree)
--     replaceSubTrees = Set.filter (\(_,t) -> isInfixOf [getTreeCat t] replaceCats) pSubTrees
--     -- Get all possible combinations of them
--     combinations :: [[(Path,TTree)]]
--     combinations = powerList $ toList replaceSubTrees
--     -- Tiny wrapper to extract the second part of the tuples
--     extractTrees :: [(Path,TTree)] -> [TTree]
--     extractTrees =
--       map snd
--     -- Pack the parameters and results into one tuple - the generated tree, the pruned tree, the trees used to match the tree, and the removed subtrees
--     tempResults :: [(TTree,TTree,[TTree],[TTree])]
--     tempResults = map (\replaceTrees -> let deletedTrees = (extractTrees (toList pSubTrees) \\ extractTrees replaceTrees) in (gMetaTree,pMetaTree,extractTrees replaceTrees,deletedTrees)) combinations
--     -- Combine the new possible trees
--     newTrees :: [TTree]
--     newTrees = concatMap (\(p1,_,p3,_) -> combineTrees p1 p3) tempResults
--     -- Compute the costs for each of these trees
--     costs :: [Cost]
--     costs = map (\(p1,p2,_,p4) -> computeCosts p1 p2 p4) tempResults
--   in
--     -- Sort by cost
--     sortBy (\(c1,_) (c2,_) -> compare c1 c2) $ zip costs newTrees

-- TODO comments and tests
hasMetas :: TTree -> Bool
hasMetas (TMeta _) = True
hasMetas (TNode _ _ children) = or $ map hasMetas children

-- Code ideas provided by Peter
    -- tempResults :: [(TTree,TTree,[TTree],[TTree])]
    -- tempResults = [ (gMetaTree, pMetaTree, extractedTrees, deletedTrees, newTree, cost)
    --               |
    --                 replaceTrees <- combinations,
    --                 let deletedTrees = extractTrees (toList pSubTrees) \\ extractTrees replaceTrees,
    --                 let extractedTree = extractTrees replaceTrees,
    --                 let newTree = combineTrees gMetaTree extractedTrees,
    --                 let cost = computeCosts gMetaTree pMetaTree deletedTrees
    --               ]
    -- -- Combine the new possible trees
    -- newTrees :: [TTree]
    -- newTrees = map (\(p1,_,p3,_) -> combineTrees p1 p3) tempResults
    -- -- Compute the costs for each of these trees
    -- costs :: [Cost]
    -- costs = map (\(p1,p2,_,p4) -> computeCosts p1 p2 p4) tempResults
