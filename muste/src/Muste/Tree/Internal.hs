{-# language DeriveGeneric, LambdaCase, UnicodeSyntax, DeriveLift #-}
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
  , toGfTree
  ) where

-- TODO Do not depend on PGF
import qualified PGF
  (CId, mkCId, Tree, wildCId, mkMeta, mkApp, showExpr)

import Data.Maybe
import Data.Aeson
import Data.Binary (Binary)
import qualified Data.Text as Text
import GHC.Generics
import Data.String
import Data.String.ToString
import Control.Monad.Fail hiding (fail)
import Text.Read (readEither)
import Data.Text.Prettyprint.Doc (Pretty(pretty))
import Text.Printf
import Language.Haskell.TH.Syntax (Lift)

import Muste.Common.SQL (FromField, ToField)
import qualified Muste.Common.SQL as SQL

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
  = TNode String FunType [TTree]
  -- A meta tree consisting just of a category type
  | TMeta Category
   -- read is broken at the moment, most likely because of the
   -- read/show instances for @CId@
  deriving (Ord, Eq, Show, Read, Generic)

deriving instance Lift TTree

instance Binary TTree

instance Pretty TTree where
  pretty = pretty . prettyTree

prettyTree ∷ TTree → String
prettyTree = PGF.showExpr mempty . toGfTree

-- parseTree ∷ MonadFail fail ⇒ String → fail TTree
-- parseTree = do
--   gfTree ← liftFailMaybe _ . PGF.readExpr
--   _ gfTree

-- liftFailMaybe ∷ MonadFail m => String → Maybe a → m a
-- liftFailMaybe err = _

-- TODO Make generalized container for @TTree@ (i.e. kind @* -> *@,
-- that way we can make suitable instances for @Foldable@,
-- @Traversable@...

-- The challenge is that these are not regular rose trees since
-- @TTree@ has the guarantee that the leafs only contain a string and
-- the internal nodes contain a @Sring@ and a `FunType`.

-- foldlTTree :: (b -> Either (String, FunType) Category -> b) -> b -> TTree -> b
-- foldlTTree f x t = case t of
--   TNode nm tp xs -> f (foldl (foldlTTree f) x xs) (Left (nm, tp))
--   TMeta cat      -> f x (Right cat)

parseString :: MonadFail m => String -> (Text.Text -> m p) -> Value -> m p
parseString errMsg f = \case
  (String s) -> f s
  val -> fail $ printf "%s: %s" errMsg (show val)

liftFailEither :: MonadFail m => Either String a -> m a
liftFailEither = either fail pure

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
  parseJSON = parseString "Muste.Tree.parseJSON @TTree"
    (liftFailEither . readEither . toString)

instance ToJSON TTree where
  toJSON = String . fromString . show

instance FromField TTree where
  fromField = SQL.fromBlob

instance ToField TTree where
  toField = SQL.toBlob

-- | The basic type of sentences and sentence formers.
data FunType
  = Fun Category [Category]
  -- ^ Contains the resulting category and the categories of the
  -- parameters.
  | NoType
  deriving (Ord, Eq, Show, Read, Generic)

deriving instance Lift FunType

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

-- FIXME Make this abstract so we can override the {To,From}JSON
-- instance for this type and avoid using this `clean_lin` function
-- which is defined in `muste-gui.js`.

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
getTreeCat (TNode _id typ _) =
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
    update pos (LNode cat _id []) = (pos + 1, LNode cat pos [])
    update pos (LNode cat _id ns) =
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
    deep (LNode _cid fid ns) _id path = if fid == id then path else broad ns id path 0
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

-- -- My attempt at replacing the above function with something that does
-- -- not need to know about @LTree@'s. I misunderstood @getPath@ and
-- -- wrote a depth first algorithm in stead.
-- getPathDF :: TTree -> Int -> Path
-- getPathDF t n = maybe mempty reverse $ evalState (aux t) n
--   where
--   aux :: TTree -> State Int (Maybe Path)
--   aux t = do
--     n <- get
--     modify pred
--     if n <= 0
--     then pure $ pure $ [0]
--     else case t of
--       TMeta{}      -> pure Nothing
--       TNode _ _ xs -> fmap (listToMaybe . catMaybes) <$> mapM step $ zip [0..] xs
--   step :: (Int, TTree) -> State Int (Maybe Path)
--   step (childNo, t) = fmap (childNo :) <$> aux t

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
replaceNode oldTree@(TNode _ _ trees) (pos:ps) newTree
  | pos >= 0 && pos < length trees =  -- subtree must exist
    let
      branch = fromJust $ selectBranch oldTree pos
    in
      replaceBranch oldTree pos (replaceNode branch ps newTree)
  | otherwise = oldTree -- if branch does not exist just do nothing
replaceNode _oldTree [] newTree =
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

-- FIXME I didn't want to place this here, it really belongs in the
-- Muste.Grammar module, but we need it here to get a 'Pretty'
-- instance for 'TTree' (we're reusing functionality in 'PGF').  This
-- is the lesser evil compared to orhpan instances.
-- | Creates a GF abstract syntax Tree from a generic tree.
toGfTree :: TTree -> PGF.Tree
toGfTree tree =
  let
    loop :: [TTree] -> Int -> (Int,[PGF.Tree])
    loop [] id = (id,[])
    loop (t:ts) id =
      let
        (nid,nt) = convert t id
        (fid,nts) = loop ts nid
      in
        (fid,nt:nts)
    convert :: TTree -> Int -> (Int,PGF.Tree)
    convert (TMeta _) id = (id + 1, PGF.mkMeta id)
    convert (TNode name _ ns) id =
      let
        (nid,nts) = loop ns id
      in
        if name == wildCard then (nid,PGF.mkApp PGF.wildCId nts) else (nid,PGF.mkApp (PGF.mkCId name) nts)
  in
    snd $ convert tree 0
