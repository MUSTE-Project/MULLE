{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
{-# Language TemplateHaskell, UndecidableInstances, OverloadedLists #-}
module Muste.Menu.New
  ( NewFancyMenu(..)
  , getNewFancyMenu
  , getMenuItems
  , Selection
  , Sentence.Linearization
  , Token.Unannotated
  , Token.Annotated(..)
  , Interval(Interval, runInterval)
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
lookupNode tree path = case Tree.selectNode tree path of
                         Just (TNode node _ _) -> node
                         _ → error "Incomplete Pattern-Match"

similarTrees :: Context -> TTree -> [TTree]
similarTrees ctxt tree = [ tree' | (_path, simtrees) <- Map.toList simmap, (_, tree') <- Set.toList simtrees ]
    where simmap = Prune.replaceTrees (ctxtGrammar ctxt) (ctxtPrecomputed ctxt) tree

-- * Exported stuff

newtype NewFancyMenu = NewFancyMenu
  { unNewFancyMenu ∷ Map Selection
    (Set (Selection, Sentence.Linearization Token.Annotated))
  }

deriving instance Show       NewFancyMenu
deriving instance Semigroup  NewFancyMenu
deriving instance Monoid     NewFancyMenu
deriving instance ToJSON     NewFancyMenu
deriving instance FromJSON   NewFancyMenu

deriving instance MonoFunctor NewFancyMenu

type instance Element NewFancyMenu
  = (Set (Selection, Sentence.Linearization Token.Annotated))

instance MonoFoldable NewFancyMenu where
  ofoldl'    f a (NewFancyMenu m) = ofoldl' f a m
  ofoldr     f a (NewFancyMenu m) = ofoldr f a m
  ofoldMap   f (NewFancyMenu m)   = ofoldMap f m
  ofoldr1Ex  f (NewFancyMenu m)   = ofoldr1Ex f m
  ofoldl1Ex' f (NewFancyMenu m)   = ofoldl1Ex' f m

instance MonoTraversable NewFancyMenu where
  otraverse f (NewFancyMenu m) = NewFancyMenu <$> otraverse f m

instance GrowingAppend NewFancyMenu where

instance Mono.SetContainer NewFancyMenu where
  type ContainerKey NewFancyMenu                 = Selection
  member k     (NewFancyMenu m)                  = Mono.member k m
  notMember k  (NewFancyMenu m)                  = Mono.notMember k m
  union        (NewFancyMenu a) (NewFancyMenu b) = NewFancyMenu $ a `Mono.union` b
  intersection (NewFancyMenu a) (NewFancyMenu b) = NewFancyMenu $ a `Mono.intersection` b
  difference   (NewFancyMenu a) (NewFancyMenu b) = NewFancyMenu $ a `Mono.difference` b
  keys         (NewFancyMenu m)                  = Mono.keys m

instance Mono.IsMap NewFancyMenu where
  type MapValue NewFancyMenu      = Element NewFancyMenu
  lookup c       (NewFancyMenu m) = Mono.lookup c m
  singletonMap c t                = NewFancyMenu $ Mono.singletonMap c t
  mapFromList as                  = NewFancyMenu $ Mono.mapFromList as
  insertMap k vs (NewFancyMenu m) = NewFancyMenu $ Mono.insertMap k vs m
  deleteMap k    (NewFancyMenu m) = NewFancyMenu $ Mono.deleteMap k m
  mapToList      (NewFancyMenu m) = Mono.mapToList m

instance Pretty NewFancyMenu where
  -- pretty = pretty . Map.toList . unNewFancyMenu
  pretty
    =   unNewFancyMenu
    >>> Map.toList
    >>> fmap @[] (fmap @((,) Selection) Set.toList)
    >>> pretty

-- | FIXME Change my name when we have moved the deprecated 'getMenu'.
getNewFancyMenu
  ∷ Sentence.IsToken a
  ⇒ Context
  → Sentence.Linearization a
  → NewFancyMenu
getNewFancyMenu c l
  = Sentence.stringRep l
  & getMenuItems c

getMenuItems :: Context -> String -> NewFancyMenu
getMenuItems ctxt str =
    collectTreeSubstitutions ctxt str &
    filterTreeSubstitutions &
    collectMenuItems ctxt


type TreeSubst = (Int, XTree, XTree)
type XTree = (TTree, [Tokn], [Node])

collectTreeSubstitutions :: Context -> String -> [TreeSubst]
collectTreeSubstitutions ctxt sentence =
    do oldtree <- parseSentence ctxt sentence
       let (oldwords, oldnodes) = linTree ctxt oldtree
       let old = (oldtree, oldwords, oldnodes)
       newtree <- similarTrees ctxt oldtree
       let (newwords, newnodes) = linTree ctxt newtree
       let new = (newtree, newwords, newnodes)
       return (old `xtreeDiff` new, old, new)

collectMenuItems :: Context -> [TreeSubst] -> NewFancyMenu
collectMenuItems ctxt substs = NewFancyMenu $ Map.fromListWith Set.union $ do
  (_cost, (_oldtree, _oldwords, oldnodes), (_newtree, newwords, newnodes)) ← substs
  let edits = alignSequences oldnodes newnodes
  let (oldselection, newselection) = splitAlignments edits
  let allnewnodes = foldl1 Annotated.mergeL
                    [ Annotated.mkLinearization ctxt t t t |
                      t <- parseSentence ctxt (unwords newwords) ]
  return (oldselection, Set.singleton (newselection, allnewnodes))


filterTreeSubstitutions :: [TreeSubst] -> [TreeSubst]
filterTreeSubstitutions substs =
    ---- simple, quadratic variant:
    keepWith directMoreExpensive substs
    ---- more optimised, only compares with substitutions with lower cost:
    ---- (1/2 the nr of comparisons, but makes no real difference in the end)
    -- do let groups = groupWith (\(cost,_,_) -> cost) substs
    --    (cheapergroups, group, _expensiver) <- split groups
    --    subst <- group
    --    guard $ isCheapest cheapergroups subst
    --    return subst
    -- where isCheapest cheapergroups (cost, old, new) =
    --           and [ mid `xtreeDiff` new >= cost |
    --                 cheaper <- cheapergroups,
    --                 (_cost, old', mid) <- cheaper, old == old' ]


keepWith :: (a → a → Bool) -> [a] -> [a]
keepWith p xs = [ x | x <- xs, not (any (p x) xs) ]

directMoreExpensive :: TreeSubst -> TreeSubst -> Bool
directMoreExpensive (cost, _, xtree) (cost', _, xtree')
    = cost' < cost && xtree' `xtreeDiff` xtree < cost

xtreeDiff :: XTree -> XTree -> Int
xtreeDiff (t,_,_) (t',_,_) = getNodes t `editDistance` getNodes t'
    where getNodes (TMeta cat) = ["?" ++ cat]
          getNodes (TNode fun _ children) = fun : concatMap getNodes children


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
    where merge edit [] = [edit]
          merge edit@((xs,i,_j), (xs',i',_j')) (((ys,_k,l), (ys',_k',l')) : edits)
              | ys == ys' = edit : mergeEdits edits
              | otherwise = merge ((xs++ys,i,l), (xs'++ys',i',l')) edits
