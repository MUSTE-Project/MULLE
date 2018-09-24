{-# OPTIONS_GHC -Wall #-}
{-# Language TemplateHaskell, UndecidableInstances, OverloadedLists #-}
module Muste.Menu.Internal
  ( Menu(..)
  , getMenu
  , getMenuItems
  , Selection(Selection)
  , Sentence.Linearization
  , Token.Unannotated
  , Token.Annotated(..)
  , Interval(Interval, runInterval)
  , Prune.PruneOpts(..)
  ) where

import Prelude ()
import Muste.Prelude
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Array as Array
import Data.MonoTraversable
import qualified Data.Containers as Mono
import Data.List (intercalate)
import Data.Aeson (ToJSONKey, FromJSONKey)
import Control.DeepSeq (NFData)

import Muste.Common
import qualified Muste.Grammar.Internal as Grammar
import Muste.Linearization.Internal
  (Linearization(..), Context, ctxtGrammar, ctxtLang, ctxtPrecomputed)
import qualified Muste.Linearization.Internal as Linearization
import Muste.Tree.Internal (TTree(..), Path)
import qualified Muste.Tree.Internal as Tree
import qualified Muste.Prune as Prune
import Data.Function ((&))
import qualified Data.Text.Prettyprint.Doc as Doc

import qualified Muste.Sentence as Sentence
import qualified Muste.Sentence.Linearization as Sentence (Linearization)
import qualified Muste.Sentence.Token as Token
import qualified Muste.Sentence.Annotated as Annotated

type Tokn = String
type Node = String

newtype Interval = Interval { runInterval ∷ (Int, Int) }

deriving instance ToJSONKey Interval
deriving instance FromJSONKey Interval
deriving instance ToJSON Interval
deriving instance FromJSON Interval
deriving instance Show Interval
deriving instance Eq Interval
instance Ord Interval where
  a `compare` b = case sizeInterval a `compare` sizeInterval b of
    EQ → runInterval a `compare` runInterval b
    x  → x
deriving instance Read Interval
deriving instance Generic Interval
instance NFData Interval where

sizeInterval ∷ Interval → Int
sizeInterval (Interval (i, j)) = j - i

newtype Selection = Selection { runSelection ∷ [Interval] }

deriving instance Read Selection
deriving instance ToJSONKey Selection
deriving instance FromJSONKey Selection
deriving instance Show Selection
deriving instance ToJSON Selection
deriving instance FromJSON Selection
instance IsList Selection where
  type Item Selection = Interval
  fromList = Selection
  toList = runSelection
deriving instance Eq Selection
instance Ord Selection where
  a `compare` b = case size a `compare` size b of
    EQ → runSelection a `compare` runSelection b
    x  → x
    where
    size ∷ Selection → Int
    size = runSelection >>> fmap sizeInterval >>> sum
deriving instance Generic Selection
instance NFData Selection where

deriving instance Semigroup Selection
deriving instance Monoid Selection

instance Pretty Selection where
  pretty (Selection sel) = Doc.braces $ pretty $ intercalate "," $ map go sel
    where go (Interval (i,j)) = show i ++ "-" ++ show j

-- * First, some basic functions and types:

parseSentence :: Context -> String -> [TTree]
parseSentence ctxt sent
  = Grammar.parseSentence (ctxtGrammar ctxt) (ctxtLang ctxt) sent

linTree :: Context -> TTree -> ([Tokn], [Node])
linTree ctxt tree = (map Linearization.ltlin lintokens, map (lookupNode tree . Linearization.ltpath) lintokens)
    where Linearization lintokens = Linearization.linearizeTree ctxt tree

lookupNode :: TTree -> Path -> Node
lookupNode tree path
  = case Tree.selectNode tree path of
    Just (TNode node _ _) -> node
    _ → error "Incomplete Pattern-Match"

similarTrees ∷ Prune.PruneOpts → Context → TTree → Set TTree
similarTrees opts c
  = Prune.replaceTrees opts (ctxtGrammar c) (ctxtPrecomputed c)

-- * Exported stuff

newtype Menu = Menu
  { unMenu ∷ Map Selection
    (Set (Selection, Sentence.Linearization Token.Annotated))
  }

deriving instance Show       Menu
deriving instance Semigroup  Menu
deriving instance Monoid     Menu
deriving instance ToJSON     Menu
deriving instance FromJSON   Menu
deriving instance Generic    Menu
instance NFData Menu where

deriving instance MonoFunctor Menu

type instance Element Menu
  = (Set (Selection, Sentence.Linearization Token.Annotated))

instance MonoFoldable Menu where
  ofoldl'    f a (Menu m) = ofoldl' f a m
  ofoldr     f a (Menu m) = ofoldr f a m
  ofoldMap   f (Menu m)   = ofoldMap f m
  ofoldr1Ex  f (Menu m)   = ofoldr1Ex f m
  ofoldl1Ex' f (Menu m)   = ofoldl1Ex' f m

instance MonoTraversable Menu where
  otraverse f (Menu m) = Menu <$> otraverse f m

instance GrowingAppend Menu where

instance Mono.SetContainer Menu where
  type ContainerKey Menu         = Selection
  member k     (Menu m)          = Mono.member k m
  notMember k  (Menu m)          = Mono.notMember k m
  union        (Menu a) (Menu b) = Menu $ a `Mono.union` b
  intersection (Menu a) (Menu b) = Menu $ a `Mono.intersection` b
  difference   (Menu a) (Menu b) = Menu $ a `Mono.difference` b
  keys         (Menu m)          = Mono.keys m

instance Mono.IsMap Menu where
  type MapValue Menu      = Element Menu
  lookup c       (Menu m) = Mono.lookup c m
  singletonMap c t        = Menu $ Mono.singletonMap c t
  mapFromList as          = Menu $ Mono.mapFromList as
  insertMap k vs (Menu m) = Menu $ Mono.insertMap k vs m
  deleteMap k    (Menu m) = Menu $ Mono.deleteMap k m
  mapToList      (Menu m) = Mono.mapToList m

instance Pretty Menu where
  pretty
    =   unMenu
    >>> Map.toList
    >>> fmap @[] (fmap @((,) Selection) Set.toList)
    >>> pretty

getMenu
  ∷ Sentence.IsToken a
  ⇒ Prune.PruneOpts
  → Context
  → Sentence.Linearization a
  → Menu
getMenu opts c l
  = Sentence.stringRep l
  & getMenuItems opts c

getMenuItems ∷ Prune.PruneOpts → Context → String → Menu
getMenuItems opts ctxt str
  = collectTreeSubstitutions opts ctxt str
  & filterTreeSubstitutions
  & collectMenuItems ctxt

type TreeSubst = (Int, XTree, XTree)
type XTree = (TTree, [Tokn], [Node])

collectTreeSubstitutions ∷ Prune.PruneOpts → Context → String → [TreeSubst]
collectTreeSubstitutions opts ctxt sentence = do
  oldtree ← parseSentence ctxt sentence
  let (oldwords, oldnodes) = linTree ctxt oldtree
  let old = (oldtree, oldwords, oldnodes)
  newtree ← Set.toList $ similarTrees opts ctxt oldtree
  let (newwords, newnodes) = linTree ctxt newtree
  let new = (newtree, newwords, newnodes)
  pure (old `xtreeDiff` new, old, new)

collectMenuItems :: Context -> [TreeSubst] -> Menu
collectMenuItems ctxt substs = Menu $ Map.fromListWith Set.union $ do
  (_cost, (_oldtree, _oldwords, oldnodes), (_newtree, newwords, newnodes)) ← substs
  let edits = alignSequences oldnodes newnodes
  let (oldselection, newselection) = splitAlignments edits
  let lins = [ Annotated.mkLinearization ctxt t t t |
                      t <- parseSentence ctxt (unwords newwords) ]
  let allnewnodes = case lins of
        []       → error "Muste.Menu.New.collectMenuItems: No linearizations."
        (x:xs) → foldl Annotated.mergeL x xs
  return (oldselection, Set.singleton (newselection, allnewnodes))


filterTreeSubstitutions :: [TreeSubst] -> [TreeSubst]
filterTreeSubstitutions = identity

keepWith :: (a → a → Bool) -> [a] -> [a]
keepWith p xs = [ x | x <- xs, not (any (p x) xs) ]

directMoreExpensive :: TreeSubst -> TreeSubst -> Bool
directMoreExpensive (cost, _, xtree) (cost', _, xtree')
    = cost' < cost && xtree' `xtreeDiff` xtree < cost

xtreeDiff :: XTree -> XTree -> Int
xtreeDiff (t,_,_) (t',_,_) = Tree.flatten t `editDistance` Tree.flatten t'


-- * LCS

type Edit a = (([a], Int, Int), ([a], Int, Int))

splitAlignments :: [Edit a] -> (Selection, Selection)
splitAlignments [] = mempty
splitAlignments (((_,i,j), (_,k,l)) : edits)
  = ([Interval (i, j)] <> oldselection, [Interval (k, l)] <> newselection)
  where (oldselection, newselection) = splitAlignments edits

alignSequences :: Eq a => [a] -> [a] -> [Edit a]
alignSequences xs ys = mergeEdits $ snd $ a Array.! (0,0)
    where n = length xs
          m = length ys
          a = Array.array ((0,0),(n,m)) $ l0 ++ l1 ++ l2 ++ l3
          l0 = [((n,m), (fromInteger @Int 0, []))]
          l1 = [((i,m), f1 x i) | (x,i) <- zip xs [0..n-1]]
          f1 x i = (del, (([x],i,i+1), ([],m,m)) : dledits)
              where (del, dledits) = a Array.! (i+1,m)
          l2 = [((n,j), f2 y j) | (y,j) <- zip ys [0..m-1]]
          f2 y j = (ins, (([],n,n), ([y],j,j+1)) : inedits)
              where (ins, inedits) = a Array.! (n,j+1)
          l3 = [((i,j), f3 x y i j) | (x,i) <- zip xs [0..], (y,j) <- zip ys [0..]]
          f3 x y i j
              | x == y     = (eqs+1, (([x],i,i+1), ([x],j,j+1)) : eqedits)
              | ins == del = (ins,   (([x],i,i+1), ([y],j,j+1)) : eqedits)
              | ins > del  = (ins,   (([],i,i), ([y],j,j+1)) : inedits)
              | otherwise  = (del,   (([x],i,i+1), ([],j,j)) : dledits)
              where (eqs, eqedits) = a Array.! (i+1,j+1)
                    (ins, inedits) = a Array.! (i,j+1)
                    (del, dledits) = a Array.! (i+1,j)

mergeEdits :: Eq a => [Edit a] -> [Edit a]
mergeEdits [] = []
mergeEdits (edit@((xs,_,_), (xs',_,_)) : edits)
    | xs == xs' = mergeEdits edits
    | otherwise = merge edit edits
    where
    merge e [] = [e]
    merge e@((xs0,i,_j), (xs0',i',_j')) (((ys,_k,l), (ys',_k',l')) : edits')
        | ys == ys' = e : mergeEdits edits
        | otherwise = merge ((xs0++ys,i,l), (xs0'++ys',i',l')) edits'
