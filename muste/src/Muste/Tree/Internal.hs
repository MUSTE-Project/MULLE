{-# language DeriveGeneric, LambdaCase #-}
{- | This Module is the internal implementation behind the module 'Muste.Tree' -}
module Muste.Tree.Internal
  ( Path
  , getPath
  , getAllPaths
  , Pos
  , Category
  , maxDepth
  , getTreeCat
  , replaceNode
  -- FIXME Are we sure we should export this?
  , selectNode
  , isValid
  , countNodes
  , countMatchedNodes
  , TTree(TNode,TMeta)
  , FunType(Fun, NoType)
  ) where

-- TODO Do not depend on PGF
import qualified PGF (CId, mkCId)

import Data.Maybe
import Data.Aeson
import Data.Binary (Binary)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Data.Text.Lazy as LText
import qualified Data.Text.Lazy.Encoding as LText
import qualified Data.Binary as Binary
import qualified Data.ByteString.Lazy as LBS
import GHC.Generics
import Control.Monad.State
import Data.String
import Data.String.ToString

import qualified Database.SQLite.Simple as SQL
import Database.SQLite.Simple.ToField (ToField)
import qualified Database.SQLite.Simple.ToField as SQL
import Database.SQLite.Simple.FromField (FromField(fromField))
import qualified Database.SQLite.Simple.FromField as SQL

import Muste.Common

-- * Trees

-- TODO Make this abstract (and instance of @IsString@).  One
-- challenge here is that we depend on the specific implementation of
-- 'Read', 'Show' and possibly other things.
-- | A semantic category
type Category = String

-- | = Typed Trees
--
-- This is a representation of gramatically structured natural
-- languages sentences.  The representation lends ideas from type
-- theory (hence the name 'TTree' @~@ /Typed Trees/).
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

instance Binary TTree

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

parseString :: (Text.Text -> p) -> Value -> p
parseString f = \case
  (String s) -> f s
  _ -> todo

-- I've experimented with different ways of serializing this data.
-- Since the client don't need direct access to 'TTree''s it makes
-- sense to just serialize this as efficiently as possible.  I though
-- I was smart and that we could derive @Binary@ for 'TTree' and then
-- use a base 64 encoding of this data, but this turned out to take up
-- more space than the naive approach of just using show/read.  For
-- more information please see this commit:
--
-- commit 824245b5062e0b989ac70782be1ed4527b2ec903
-- Author: Frederik Hanghøj Iversen <fhi.1990@gmail.com>
-- Date:   Sun Jul 22 14:25:46 2018 +0200
--
--     [WIP] Experiment with different encodings
instance FromJSON TTree where
  parseJSON = parseString (pure . read . toString)

instance ToJSON TTree where
  toJSON = String . fromString . show

-- FIXME Do I really need to do two three steps of encoding?  Is it
-- not possible to jump directly from binary to a 'Text.Text' (the
-- strict variant).
binaryToText :: Binary a => a -> Text.Text
binaryToText = LText.toStrict . LText.decodeUtf8 . Binary.encode

-- FIXME Similiar issue as for 'binaryToJSON'.
binaryFromText :: Binary c => Text.Text -> c
binaryFromText = Binary.decode . LBS.fromStrict . Text.encodeUtf8

instance FromField TTree where
  fromField fld = case SQL.fieldData fld of
    SQL.SQLText t -> pure $ binaryFromText t
    _ -> todo

todo :: a
todo = error "Muste.Tree.Internal: TODO More descriptive error message"

instance ToField TTree where
  toField = SQL.SQLText . binaryToText

-- | The basic type of sentences and sentence formers.
data FunType
  = Fun
    { _category :: Category -- ^ The resulting category
    , _params :: [Category] -- ^ The categories of the parameters.
    }
  | NoType
  deriving (Ord, Eq, Show, Read, Generic)

instance Binary FunType

-- | Generic class for trees
class Show t => TreeC t where
  -- | The function 'selectNode' returns a subtree at a given 'Path'
  -- if it exists.
  selectNode :: t -> Path -> Maybe t
  -- | The function 'selectNode' returns a subtree at a given node if
  -- it exists.
  selectBranch :: t -> Int -> Maybe t

-- FIXME Consider making abstract.
-- | Position in a path
type Pos = Int

-- FIXME Consider making abstract.
-- FIXME Another idea for indexing into a tree would be to a graph.
-- | A path in a tree.  Used by e.g. linearization for indexing into
-- the tree.
type Path = [Pos]

-- | A generic tree with types is in TreeC class.  The existence of
-- this class is a legacy from when there existed multiple
-- representations.
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

-- | The function 'isValid' "type checks" a 'TTree'
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
getTreeCat :: TTree -> Category
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

-- | The function 'getAllPaths' returns all paths in a 'TTree'
getAllPaths :: TTree -> [Path]
getAllPaths t =
  let 
    paths (TMeta _) = []
    paths (TNode _ _ []) = []
    paths (TNode _ _ cs) =
      let zips = zip [0..] cs in
      [[c]|(c,_) <- zips] ++ (concat $ map (\(p,c) -> map (p:) $ paths c) $ zips)
  in
    []:paths t
         
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

-- | Counts the (internal and external) nodes in the tree.
countNodes :: TTree -> Int
countNodes (TMeta _) = 1
countNodes (TNode _ _ []) = 1
countNodes (TNode _ _ ts) = 1 + (sum $ map countNodes ts)

countMatchedNodes :: TTree -> TTree -> Int
countMatchedNodes tree1 tree2 =
  let
    paths = getAllPaths tree1
  in
    length $ filter (\p -> selectNode tree1 p == selectNode tree2 p) paths
