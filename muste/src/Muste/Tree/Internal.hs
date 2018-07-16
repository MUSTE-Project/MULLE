{-# LANGUAGE DeriveGeneric #-}
{- | This Module is the internal implementation behind the module 'Muste.Tree' -}
module Muste.Tree.Internal
  ( Path
  , getPath
  , getPathes
  , Pos
  , maxDepth
  , getTreeCat
  , replaceNode
  , selectNode
  , isValid
  , showTree
  , countNodes
  , countMatchedNodes
  , TTree(TNode,TMeta)
  , FunType(Fun, NoType)
  ) where

-- TODO Do not depend on PGF
import qualified PGF (CId, mkCId)

import Data.Maybe
import Data.Aeson
import GHC.Generics

import Common

import Control.Monad.State

-- * Trees

-- TODO Make this abstract (and instance of @IsString@).  One
-- challenge here is that we depend on the specific implementation of
-- 'Read', 'Show' and possibly other things.
-- | A semantic category
type Category = String

-- | A generic tree with types
data TTree
   -- Regular node consisting of a function name, function type and
   -- possible subtrees
  = TNode
    { _functionName :: String
    , _functionType :: FunType
    , _subTrees :: [TTree]
    }
  -- A meta tree consisting just of a category type
  | TMeta { _categoryType :: Category }
   -- read is broken at the moment, most likely because of the
   -- read/show instances for @CId@
  deriving (Ord, Eq, Show, Read, Generic)

-- TODO Make generalized container for @TTree@ (i.e. kind @* -> *@,
-- that way we can make suitable instances for @Foldable@,
-- @Traversable@...

-- The challenge is that these are not regular rose trees since
-- @TTree@ has the guarantee that the leafs only contain a string and
-- the internal nodes contain a @Sring@ and a `FunType`.

foldlTTree :: (b -> Either (String, FunType) Category -> b) -> b -> TTree -> b
foldlTTree f x t = case t of
  TNode nm tp xs -> f (foldl (foldlTTree f) x xs) (Left (nm, tp))
  TMeta cat      -> f x (Right cat)

-- traverseTTree
--   :: Applicative f
--   => (  Either (String, FunType) Category
--     -> f (Either (String, FunType) Category)
--     )
--   -> TTree
--   -> f TTree
-- traverseTTree f t = case t of
--   TNode nm tp xs -> (\xss -> _) <$> traverse (traverseTTree f) xs
--   TMeta cat      -> t <$ f (Right cat)

-- instance ToJSON TTree where
--     toEncoding = genericToEncoding defaultOptions

instance FromJSON TTree

-- | Type @FunType@ consists of a @String@ that is the the result
-- category and @[String]@ are the categories of the paramaters.
data FunType
  = Fun { _category :: Category, _params :: [Category] }
  | NoType
  deriving (Ord, Eq, Show, Read, Generic)

instance ToJSON FunType where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON FunType

-- | Generic class for trees
class Show t => TreeC t where
  -- | The function 'selectNode' returns a subtree at given 'Path' if it exists
  selectNode :: t -> Path -> Maybe t
  -- | The function 'selectNode' returns a subtree at given node if it exists
  selectBranch :: t -> Int -> Maybe t

{-# DEPRECATED showTree "Just use @show@" #-}
showTree :: TreeC t => t -> String
showTree = show

-- FIXME Consider making abstract.
-- | Position in a path
type Pos = Int

-- FIXME Consider making abstract.
-- | Path in a tree
type Path = [Pos]

-- | A generic tree with types is in TreeC class
instance TreeC TTree where
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
-- | The function 'listReplace' replaces an element in a 'List' if the
-- position exists
listReplace :: [a] -> Pos -> a -> [a]
listReplace list pos a
  | 0 <= pos && pos < length list = -- pos in list -> replace it
      let
        (pre,_:post) = splitAt pos list
      in
        pre ++ (a:post)
  | otherwise = list -- Element not in the list -> return the same list instead

-- | The function 'isValid' "type-checks" a 'TTree'
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
    
-- | The function 'getTreeCat' gives the root category of a 'TTree',
-- returns 'wildCId' on missing type
getTreeCat :: TTree -> String
getTreeCat (TNode id typ _) =
  case typ of {
    (Fun cat _) -> cat ;
    NoType -> wildCard
    }
getTreeCat (TMeta cat) = cat

data LTree = LNode PGF.CId Int [LTree] | LLeaf deriving (Show,Eq)

-- | A generic tree with types is in TreeC class
instance TreeC LTree where
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
  selectBranch (LLeaf) _ = Nothing
  selectBranch (LNode _ _ [] ) _ = Nothing
  selectBranch (LNode _ _ trees) i
    | i < 0 || i >= length trees = Nothing
    | otherwise = Just (trees !! i)

-- | Creates a labeled LTree from a TTree
ttreeToLTree :: TTree -> LTree
ttreeToLTree tree =
  let
    -- Convert structure without caring about labels
    convert (TMeta cat) = LNode (PGF.mkCId cat) (-1) [LNode (PGF.mkCId "_") (-1) [LLeaf]]
    convert (TNode _ (Fun cat _) []) = LNode (PGF.mkCId cat) (-1) []
    convert (TNode _ (Fun cat _) ts) = LNode (PGF.mkCId cat) (-1) (map convert ts)
    convert rest = error $ "Could not convert tree due to lack of types" ++ show rest

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

-- | Calculates the @Path@ to a node given an index. The index refers
-- to the the numbering nodes in breadth first search order.  The empty
-- list is used as an out of bounds value.
--- | The function 'getPath' finds a path to a node with a given label in a labeled tree
getPath :: TTree -> Int -> Path
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
    reverse $ deep (ttreeToLTree ltree) id []

-- My attempt at replacing the above function with something that does
-- not need to know about @LTree@'s. I misunderstood @getPath@ and
-- wrote a depth first algorithm in stead.
getPathDF :: TTree -> Int -> Path      
getPathDF t n = maybe mempty reverse $ evalState (aux t) n
  where
  aux :: TTree -> State Int (Maybe Path)
  aux t = do
    n <- get
    modify pred
    if n <= 0
    then pure $ pure $ [0]
    else case t of
      TMeta{}      -> pure Nothing
      TNode _ _ xs -> fmap (listToMaybe . catMaybes) <$> mapM step $ zip [0..] xs
  step :: (Int, TTree) -> State Int (Maybe Path)
  step (childNo, t) = fmap (childNo :) <$> aux t

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

countNodes :: TTree -> Int
countNodes (TMeta _) = 1
countNodes (TNode _ _ []) = 1
countNodes (TNode _ _ ts) = 1 + (sum $ map countNodes ts)

countMatchedNodes :: TTree -> TTree -> Int
countMatchedNodes tree1 tree2 =
  let
    pathes = getPathes tree1
  in
    length $ filter (\p -> selectNode tree1 p == selectNode tree2 p) pathes
