{-# OPTIONS_GHC -Wall -Wno-name-shadowing -Wno-incomplete-patterns #-}
{-# Language
 DeriveAnyClass,
 DeriveGeneric,
 DerivingStrategies,
 GeneralizedNewtypeDeriving,
 LambdaCase,
 OverloadedStrings,
 StandaloneDeriving
#-}

{- | This Module is the internal implementation behind the module 'Muste.Tree' -}
module Muste.Tree.Internal
  ( Path
  , getPath
  , getAllPaths
  , Pos
  , Category(..)
  , maxDepth
  , getTreeCat
  , replaceNode
  -- FIXME Are we sure we should export this?
  , selectNode
  , isValid
  , treeDepth
  , countNodes
  , countMatchedNodes
  , prettyTree
  , TTree(TNode,TMeta)
  , FunType(Fun, NoType)
  , toGfTree
  , flatten
  , treeDiff
  , foldMapTTree
  , cIdToCat
  ) where

import Muste.Util (toBlob, fromBlob)
import Database.SQLite.Simple.ToField (ToField(..))
import Database.SQLite.Simple.FromField (FromField(..))

-- TODO Do not depend on PGF
import qualified PGF (CId, utf8CId, Tree, wildCId, mkMeta, mkApp, showExpr, showCId)

import Control.Category ((>>>))
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)

import Data.Aeson
import Data.Binary (Binary)
import Data.Data (Typeable)
import Data.Maybe (fromJust)
import Data.String (IsString(fromString))
import Data.String.Conversions (convertString)
import Data.String.ToString
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc (Pretty(pretty))
import Text.Printf (printf)
import Text.Read (readEither)

import Muste.Util (editDistance, wildCard)


-- * Trees

-- TODO Make this abstract (and instance of @IsString@).  One
-- challenge here is that we depend on the specific implementation of
-- 'Read', 'Show' and possibly other things.
-- | A semantic category
newtype Category = Category { unCategory :: Text }

deriving newtype instance Ord Category
deriving newtype instance Show Category
deriving newtype instance Read Category
deriving newtype instance Eq Category
deriving newtype instance Semigroup Category
deriving newtype instance Monoid Category
deriving newtype instance NFData Category
deriving newtype instance Typeable Category
deriving newtype instance Binary Category
deriving newtype instance IsString Category

prettyCat :: Category -> String
prettyCat (Category c) = Text.unpack c

-- * = Typed Trees
--
-- This is a representation of gramatically structured natural
-- languages sentences.  The representation lends ideas from type
-- theory (hence the name 'TTree' @~@ /Typed Trees/).

-- | A generic tree with types
data TTree
   -- Regular node consisting of a function name, function type and
   -- possible subtrees
  = TNode Category FunType [TTree]
  -- A meta tree consisting just of a category type
  | TMeta Category
   -- read is broken at the moment, most likely because of the
   -- read/show instances for @CId@
  deriving (Ord, Eq, Show, Read, Generic)

instance NFData TTree where

instance Binary TTree

instance Pretty TTree where
  pretty = pretty . prettyTree

prettyTree :: TTree -> String
prettyTree (TNode cat fun trees) =
  "(" ++ prettyFunType fun ++ ":" ++ prettyCat cat ++
  concat [ " " ++ prettyTree t | t <- trees ] ++ ")"
prettyTree (TMeta cat) = "?:" ++ prettyCat cat

-- | Flattening a 'TTree' into a list of its function nodes.
-- This is reversable, if the grammar is known.
-- TODO: merge with 'Muste.Grammar.Internal.getFunction.getF'?
-- TODO: this should use an accumulator, right?
flatten :: TTree -> [Category]
flatten (TMeta cat) = pure $ "?" <> cat
flatten (TNode x _ ts) = x : concatMap flatten ts

-- | Edit distance between trees.
-- This is calculated by the Levenshtein distance between the list of
-- function nodes in each of the trees
treeDiff :: TTree -> TTree -> Int
treeDiff t t' = flatten t `editDistance` flatten t'


parseString :: Monad m => String -> (Text -> m p) -> Value -> m p
parseString errMsg f = \case
  (String s) -> f s
  val -> fail $ printf "%s: %s" errMsg (show val)

liftFailEither :: Monad m => Either String a -> m a
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
  fromField = fromBlob

instance ToField TTree where
  toField = toBlob

-- | The basic type of sentences and sentence formers.
data FunType
  = Fun Category [Category]
  -- ^ Contains the resulting category and the categories of the
  -- parameters.
  | NoType
  deriving (Ord, Eq, Show, Read, Generic)

instance Binary FunType

instance NFData FunType where
  -- Generic derivation

-- | Generic class for trees
class Show t => TreeC t where
  -- | The function 'selectNode' returns a subtree at a given 'Path'
  -- if it exists.
  selectNode :: t -> Path -> Maybe t
  -- | The function 'selectNode' returns a subtree at a given node if
  -- it exists.
  selectBranch :: t -> Int -> Maybe t

prettyFunType :: FunType -> String
prettyFunType (Fun c _) = prettyCat c
prettyFunType (NoType)  = "?"

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
        if (t == ccats) && all fst vs then (True,Nothing)
        else if null brokenPath then (False, Just $ reverse path) else (False, Just $ reverse $ fromJust $ snd $ head brokenPath)
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
  selectBranch LLeaf _ = Nothing
  selectBranch (LNode _ _ [] ) _ = Nothing
  selectBranch (LNode _ _ trees) i
    | i < 0 || i >= length trees = Nothing
    | otherwise = Just (trees !! i)

-- | Creates a labeled LTree from a TTree
ttreeToLTree :: TTree -> LTree
ttreeToLTree tree =
  let
    -- Convert structure without caring about labels
    convert (TMeta cat) = LNode (catToCid cat) (-1) [LNode (catToCid "_") (-1) [LLeaf]]
    convert (TNode _ (Fun cat _) []) = LNode (catToCid cat) (-1) []
    convert (TNode _ (Fun cat _) ts) = LNode (catToCid cat) (-1) (map convert ts)
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

catToCid :: Category -> PGF.CId
catToCid = unCategory >>> convertString >>> PGF.utf8CId

-- FIXME A 'PGF.CId' is just a newtype wrapper around a 'ByteString'.
-- If we could just get at that somehow.  If [this PR][PR#9] goes
-- through we will be able to do this.
--
-- [PR#9]: https://github.com/GrammaticalFramework/gf-core/pull/9
cIdToCat :: PGF.CId -> Category
cIdToCat = PGF.showCId >>> Text.pack >>> Category

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
      [[c]|(c,_) <- zips] ++ concatMap (\(p,c) -> map (p:) $ paths c) zips
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

-- | Returns the depth of the tree. Metas are not counted.
treeDepth :: TTree -> Int
treeDepth (TMeta _) = 0
treeDepth (TNode _ _ []) = 1
treeDepth (TNode _ _ ts) = 1 + maximum (map treeDepth ts)

-- | Counts the function nodes in the tree. Metas are not counted.
countNodes :: TTree -> Int
countNodes (TMeta _) = 0
countNodes (TNode _ _ []) = 1
countNodes (TNode _ _ ts) = 1 + sum (map countNodes ts)

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
        if name == wildCard then (nid,PGF.mkApp PGF.wildCId nts) else (nid,PGF.mkApp (catToCid name) nts)
  in
    snd $ convert tree 0

{-# INLINE foldMapTTree #-}
-- | If 'TTree' was an instance of 'Foldable' then 'foldMap' would look
-- something like this.
foldMapTTree
  :: Monoid w
  => (Category -> FunType -> w)
  -> TTree
  -> w
foldMapTTree f = \case
  TMeta{} -> mempty
  TNode s t ts -> f s t <> foldMap (foldMapTTree f) ts
