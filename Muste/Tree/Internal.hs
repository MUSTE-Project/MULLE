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
data TTree = TNode String FunType [TTree] -- Regular node consisting of a function name, function type and possible subtrees
           | TMeta String -- A meta tree consisting just of a category type
           deriving (Ord,Eq,Show,Read) -- read is broken at the moment, most likely because of the CId

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
      closure grammar depth (mkApp (mkCId start) [])

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

-- | The function 'getChildCats' extracts the root category of each childtree
getChildCats :: TTree -> [String]
getChildCats (TMeta _) = []
getChildCats (TNode _ _ trees) =
  let
    extract :: TTree -> String
    extract (TMeta cat) = cat
    extract (TNode _ NoType _) = "?"
    extract (TNode _ (Fun cat _) _) = cat
  in
    map extract trees
                 
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

-- | The function 'hasMetas' is a predicate that is true if a 'TTree' contains any 'TMeta' nodes
hasMetas :: TTree -> Bool
hasMetas (TMeta _) = True
hasMetas (TNode _ _ children) = or $ map hasMetas children

isValid :: TTree -> (Bool,Maybe Path)
isValid t =
  let
    check :: TTree -> Path -> (Bool,Maybe Path)
    check (TMeta _) _ = (True,Nothing)
    check (TNode _ NoType []) _ = (True,Nothing)
    check (TNode _ (Fun _ t) c) path =
      let
        ccats = map getTreeCat c
        vs = map (\(p,t) -> check t (p:path)) $ zip [0..] c
        brokenPath = filter (not . fst) vs
      in
        if (t == ccats) && (and $ map fst vs)then (True,Nothing) 
        else if null brokenPath then (False, Just $ reverse path) else (False, Just $ reverse $ fromJust $ snd $ head $ brokenPath)
    check _ path = (False, Just $ reverse path)
  in
    check t []
    
-- | The function 'getTreeCat' gives the root category of a 'TTree', returns 'wildCId' on missing type
getTreeCat :: TTree -> String
getTreeCat (TNode id typ _) =
  case typ of {
    (Fun cat _) -> cat ;
    NoType -> wildCard
    }
getTreeCat (TMeta cat) = cat

-- | The function 'gfAbsTreeToTTree' creates a 'TTree' from an GFabstract syntax 'Tree' and a PGF. Handles only 'EApp' and 'EFun'. Generates 'TMeta' 'wildCId' in unsupported cases
gfAbsTreeToTTreeWithPGF :: PGF -> GFAbsTree -> TTree
gfAbsTreeToTTreeWithPGF pgf (EFun f) =
  let
    typ = getFunTypeWithPGF pgf f
  in
    TNode (showCId f) typ []
gfAbsTreeToTTreeWithPGF pgf (EApp e1 e2) =
  let
    (TNode name typ sts) = gfAbsTreeToTTreeWithPGF pgf e1
    st2 = gfAbsTreeToTTreeWithPGF pgf e2
  in
    TNode name typ (sts ++ [st2])
gfAbsTreeToTTreeWithPGF pgf _ = TMeta wildCard

-- | The function 'gfAbsTreeToTTree' creates a 'TTree' from an GFabstract syntax 'Tree' and a Grammar. Othewise  similar to gfAbsTreeToTTreeWithPGF
gfAbsTreeToTTreeWithGrammar :: Grammar -> GFAbsTree -> TTree
gfAbsTreeToTTreeWithGrammar g (EFun f) =
  let
    typ = getFunTypeWithGrammar g (showCId f)
  in
    TNode (showCId f) typ []
gfAbsTreeToTTreeWithGrammar g (EApp e1 e2) =
  let
    (TNode name typ sts) = gfAbsTreeToTTreeWithGrammar g e1
    st2 = gfAbsTreeToTTreeWithGrammar g e2
  in
    TNode name typ (sts ++ [st2])
gfAbsTreeToTTreeWithGrammar _ _ = TMeta wildCard

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
        if name == wildCard then (nid,mkApp wildCId nts) else (nid,mkApp (mkCId name) nts)
  in
    snd $ convert tree 0

-- | Creates a labeled LTree from a TTree
ttreeToLTree :: TTree -> LTree
ttreeToLTree tree =
  let
    -- Convert structure without caring about labels
    convert (TMeta cat) = LNode (mkCId cat) (-1) [LNode (mkCId "_") (-1) [LLeaf]]
    convert (TNode _ (Fun cat _) []) = LNode (mkCId cat) (-1) []
    convert (TNode _ (Fun cat _) ts) = LNode (mkCId cat) (-1) (map convert ts)
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

-- | The function 'getPath' finds a path to a node with a given label in a labeled tree
getPath :: LTree -> Int -> Path
getPath ltree id = 
  let
    deep :: LTree -> Int -> Path -> Path
    deep LLeaf _ _ = []
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
    reverse $ deep ltree id []

-- | The function 'maxDepth' gets the length of the maximum path between root and a leaf (incl. meta nodes) of a 'TTree'
maxDepth :: TTree -> Int
maxDepth (TMeta _) = 1
maxDepth (TNode _ _ []) = 1
maxDepth (TNode _ _ trees) =
  1 + maximum ( map maxDepth trees )

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

-- | The function 'getMetaLeafCatsSet' returns set of the categories of all meta leaves
getMetaLeafCatsSet :: TTree -> Set String
getMetaLeafCatsSet (TMeta id) = Set.singleton id
getMetaLeafCatsSet (TNode _ _ trees) = Set.unions $ map getMetaLeafCatsSet trees

-- | The function 'getMetaLeafCatsList' returns set of the categories of all meta leaves
getMetaLeafCatsList :: TTree -> [String]
getMetaLeafCatsList (TMeta id) = [id]
getMetaLeafCatsList (TNode _ _ trees) = concat $ map getMetaLeafCatsList trees

-- | The function 'getMetaPaths' generates alist of all pathes to metas
getMetaPaths :: TTree -> [(Path,String)]
getMetaPaths tree =
  let
    withPath :: TTree -> Path -> [(Path,String)]
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

-- | The function 'combineToSet' applies a 'Rule' to a 'TTree' generating all possible new meta trees, the depth parameter limits the search for metas to be replaced. Returns a list of trees.
combineToSet :: TTree -> Int -> Rule -> Set TTree
combineToSet tree depth rule =
  let
    ruleCat :: String
    ruleCat = getRuleCat rule
    -- Find all meta-nodes that match the category of the rule
    filteredMetas :: [(Path,String)]
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

-- | The function 'combineList' applies a 'Rule' to a 'TTree' generating all possible new meta trees, the depth parameter limits the search for metas to be replaced. Returns a list of trees.
combineToList :: TTree -> Int -> Rule -> [TTree]
combineToList tree depth rule =
  let
    ruleCat :: String
    ruleCat = getRuleCat rule
    -- Find all meta-nodes that match the category of the rule
    filteredMetas :: [(Path,String)]
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


-- | The function 'extendTreeToSet' extends a 'TTree' by applying all applicable rules from a 'Grammar' once. It returns a Set of TTrees
extendTreeToSet :: Grammar -> TTree -> Int -> Set TTree
extendTreeToSet grammar tree depth =
  let
      -- Get all meta-leaves ...
      metaLeaves :: Set String
      metaLeaves = getMetaLeafCatsSet tree
      -- ... and grammar rules for them
      rules :: Set Rule
      rules = getRulesSet (getAllRules grammar) $ toList metaLeaves
  in
    -- Combine tree with the rules
    Set.unions $ toList $ Set.map (combineToSet tree depth) rules

-- | The function 'extendTree' extends a 'TTree' by applying all applicable rules from a 'Grammar' once. It returns a List of TTrees
extendTreeToList :: Grammar -> TTree -> Int -> [TTree]
extendTreeToList grammar tree depth =
  let
      -- Get all meta-leaves ...
      metaLeaves :: [String]
      metaLeaves = getMetaLeafCatsList tree
      -- ... and grammar rules for them
      rules :: [Rule]
      rules = getRulesList (getAllRules grammar) metaLeaves
  in
    -- Combine tree with the rules
    concatMap (combineToList tree depth) rules
    
-- | The function 'generate' generates all possible 'TTree's with given root-category up to a maximum height
generateSet :: Grammar -> String -> Int -> Set TTree
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
        extended = extendTreeToSet grammar tree depth -- these are already part of the result
        activeTrees = trees ++ filter (filterTree depth) (toList (Set.delete tree extended))
      in
        Set.union (Set.singleton tree) $ Set.union extended (loop activeTrees)
  in
    loop [TMeta cat]

-- | The function 'generate' generates all possible 'TTree's with given root-category up to a maximum height
generateListSimple :: Grammar -> String -> Int -> [TTree]
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
        extendedTrees = concatMap (\t -> extendTreeToList grammar t depth) trees -- these are already part of the result
      in
        --trace (show trees) $
        nub $ trees ++ loop extendedTrees
  in
    loop [TMeta cat]


generateListWithGrammar :: Grammar -> CId -> Int -> [TTree]
generateListWithGrammar grammar startCat depth =
  let
    trees = generateAllDepth (pgf grammar) (fromJust $ readType $ showCId startCat) (Just depth)
  in
--    map (gfAbsTreeToTTree $ pgf grammar) trees
        map (gfAbsTreeToTTreeWithGrammar grammar) trees


