{- | This Module is the internal implementation behind the module 'Muste.Tree' -}
module Muste.Tree.Internal where

import PGF hiding (showType,checkType,parse)
import PGF.Internal hiding (showType)
import Data.Maybe
import Muste.Grammar
import Muste.Feat

-- | Generic class for trees
class TreeC t where
  showTree :: t -> String
  -- | The function 'selectNode' returns a subtree at given 'Path' if it exists
  selectNode :: t -> Path -> Maybe t
  -- | The function 'selectNode' returns a subtree at given node if it exists
  selectBranch :: t -> Int -> Maybe t

-- | Position in a path
type Pos = Int

-- | Path in a tree
type Path = [Pos]

-- | Rename GF abstract syntax tree (from PGF)
type GFAbsTree = Tree

-- | A labeled tree - just a template to match labels to paths
data LTree = LNode CId Int [LTree] | LLeaf deriving (Show,Eq)

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

-- | The function 'isValid' "type-checks a 'TTree'
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

-- | The function 'gfAbsTreeToTTree' creates a 'TTree' from an GFabstract syntax 'Tree' and a Grammar. Othewise  similar to gfAbsTreeToTTreeWithPGF
gfAbsTreeToTTree :: Grammar -> GFAbsTree -> TTree
gfAbsTreeToTTree g (EFun f) =
  let
    typ = getFunType g (showCId f)
  in
    TNode (showCId f) typ []
gfAbsTreeToTTree g (EApp e1 e2) =
  let
    (TNode name typ sts) = gfAbsTreeToTTree g e1
    st2 = gfAbsTreeToTTree g e2
  in
    TNode name typ (sts ++ [st2])
gfAbsTreeToTTree _ _ = TMeta wildCard

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

-- | The function 'getPathes' returns all pathes in a 'TTree'
getPathes :: TTree -> [Path]
getPathes t = 
  let 
    pathes (TMeta _) = []
    pathes (TNode _ _ []) = []
    pathes (TNode _ _ cs) =
      let zips = zip [0..] cs in
      [[c]|(c,_) <- zips] ++ (concat $ map (\(p,c) -> map (p:) $ pathes c) $ zips)
  in
    []:pathes t
         
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

-- | The function 'generateTrees' generates a list of 'TTree's up to a certain depth given a grammar. Powered by the magic of feat
generateTrees :: Grammar -> String -> Int -> [TTree]
generateTrees grammar cat size =
  let
    feats = map (\d -> let f = feat grammar in (featCard f cat d,featIth f cat d)) [0..size]
  in
    concatMap (\(max,fs) -> map fs [0..max-1]) feats

