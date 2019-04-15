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
module Muste.Tree
  ( Path
  , getPath
  , getAllPaths
  , Pos
  , Category(Category, unCategory)
  , maxDepth
  , getTreeCat
  , replaceNode
  , selectNode
  , isValid
  , treeDepth
  , countNodes
  , countMatchedNodes
  , prettyTree
  , TTree(TNode,TMeta)
  , FunType(Fun, NoType)
  , flatten
  , treeDiff
  , foldMapTTree
  ) where

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)

import Data.Binary (Binary)
import Data.Data (Typeable)
import Data.Maybe (fromJust)
import Data.String (IsString)
-- import Data.String.ToString
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc (Pretty(pretty))
-- import Text.Read (readEither)

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
-- TODO: merge with 'Muste.Grammar.getFunction.getF'?
-- TODO: this should use an accumulator, right?
flatten :: TTree -> [Category]
flatten (TMeta cat) = pure $ "?" <> cat
flatten (TNode x _ ts) = x : concatMap flatten ts

-- | Edit distance between trees.
-- This is calculated by the Levenshtein distance between the list of
-- function nodes in each of the trees
treeDiff :: TTree -> TTree -> Int
treeDiff t t' = flatten t `editDistance` flatten t'


-- | The basic type of sentences and sentence formers.
data FunType
  = Fun Category [Category]
  -- ^ Contains the resulting category and the categories of the parameters.
  | NoType
  deriving (Ord, Eq, Show, Read, Generic)

instance Binary FunType

instance NFData FunType where
  -- Generic derivation

prettyFunType :: FunType -> String
prettyFunType (Fun c _) = prettyCat c
prettyFunType (NoType)  = "?"

-- FIXME Consider making abstract.
-- | Position in a path
type Pos = Int

-- | A path in a tree.  Used by e.g. linearization for indexing into the tree.
type Path = [Pos]

  -- | The function 'selectNode' returns a subtree at a given 'Path' if it exists.
selectNode :: TTree -> Path -> Maybe TTree
selectNode t [] = Just t
selectNode t [b] = selectBranch t b
selectNode t (hd:tl) =
  let branch = selectBranch t hd
  in case branch of {
    Just b -> selectNode b tl ;
    Nothing -> Nothing
    }

-- | The function 'selectBranch' returns a subtree at a given node if it exists.
selectBranch :: TTree -> Int -> Maybe TTree
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

-- | Calculates the @Path@ to a node given an index.
-- The index refers to the the numbering nodes in depth first search order
-- (children come before their parent).
-- The empty list is used as an out of bounds value.
getPath :: TTree -> Int -> Path
getPath tree n = (enumDFS [] tree ++ repeat []) !! n
  where enumDFS path (TMeta _) = [reverse path]
        enumDFS path (TNode _ _ children) =
          [ p | (i, child) <- zip [0..] children, p <- enumDFS (i:path) child ]
          ++ [reverse path]

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
