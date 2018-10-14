{-# OPTIONS_GHC -Wall #-}
{-# Language CPP, UndecidableInstances, OverloadedLists #-}
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
  , Prune.emptyPruneOpts
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
import Data.Aeson (ToJSONKey, toJSONKey, ToJSONKeyFunction(ToJSONKeyValue), toJSON, toEncoding,
                   FromJSONKey, fromJSONKey, FromJSONKeyFunction(FromJSONKeyValue), parseJSON)
import Control.DeepSeq (NFData)
import qualified Data.Text as Text

import qualified Muste.Grammar.Internal as Grammar
import Muste.Linearization.Internal
  (Linearization(..), Context, ctxtGrammar, ctxtLang, ctxtPrecomputed)
import qualified Muste.Linearization.Internal as Linearization
import Muste.Tree.Internal (TTree(..), Path, Category)
import qualified Muste.Tree.Internal as Tree
import qualified Muste.Prune as Prune
import Data.Function ((&))
import qualified Data.Text.Prettyprint.Doc as Doc

import qualified Muste.Sentence as Sentence
import qualified Muste.Sentence.Linearization as Sentence (Linearization)
import qualified Muste.Sentence.Token as Token
import qualified Muste.Sentence.Annotated as Annotated

#ifdef DIAGNOSTICS
import System.IO.Unsafe (unsafePerformIO)
import System.CPUTime (getCPUTime)
#endif

type Tokn = Text
type Node = Category

newtype Interval = Interval { runInterval ∷ (Int, Int) }

deriving instance ToJSONKey Interval
deriving instance FromJSONKey Interval
deriving instance ToJSON Interval
deriving instance FromJSON Interval
deriving instance Show Interval
deriving instance Eq Interval
deriving instance Ord Interval
deriving instance Read Interval
deriving instance Generic Interval
instance NFData Interval where

sizeInterval ∷ Interval → Int
sizeInterval (Interval (i, j)) = j - i

emptyInterval ∷ Interval → Bool
emptyInterval (Interval (i, j)) = i == j

newtype Selection = Selection { runSelection ∷ Set Interval }

deriving instance Read Selection
instance ToJSONKey Selection where
    toJSONKey = ToJSONKeyValue toJSON toEncoding
instance FromJSONKey Selection where
    fromJSONKey = FromJSONKeyValue parseJSON
deriving instance Show Selection
deriving instance ToJSON Selection
deriving instance FromJSON Selection
instance IsList Selection where
  type Item Selection = Interval
  fromList = Selection . Set.fromList
  toList = Set.toList . runSelection
deriving instance Eq Selection
instance Ord Selection where
  a `compare` b = case size a `compare` size b of
    EQ → runSelection a `compare` runSelection b
    x  → x
    where
    size ∷ Selection → Int
    size = runSelection >>> Set.map sizeInterval >>> sum
deriving instance Generic Selection
instance NFData Selection where

deriving instance Semigroup Selection
deriving instance Monoid Selection

instance Pretty Selection where
  pretty sel = Doc.braces $ pretty $ intercalate "," $ map go $ Set.toList $ runSelection sel
    where go (Interval (i,j)) = show i ++ "-" ++ show j

-- * First, some basic functions and types:

parseSentence :: Context -> Text -> [TTree]
parseSentence ctxt sent
  = Grammar.parseSentence (ctxtGrammar ctxt) (ctxtLang ctxt) sent

linTree :: Context -> TTree -> ([Tokn], [Node])
linTree ctxt tree = (toks, nods)
  where
  toks ∷ [Tokn]
  toks = Linearization.ltlin <$> lintokens
  nods = lookupNode tree . Linearization.ltpath <$> lintokens
  Linearization lintokens = Linearization.linearizeTree ctxt tree

lookupNode :: TTree -> Path -> Node
lookupNode tree path
  = case Tree.selectNode tree path of
    Just (TNode node _ _) -> node
    _ → error "Incomplete Pattern-Match"

similarTrees ∷ Prune.PruneOpts → Context → [TTree] → [(TTree, TTree)]
similarTrees opts ctxt
  = Prune.replaceAllTrees opts (ctxtPrecomputed ctxt)

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

getMenuItems ∷ Prune.PruneOpts → Context → Text → Menu
getMenuItems opts ctxt sentence
  = parseSentence ctxt sentence
  & diagnose "Context"        showctxt showopts (\x -> x)
  & diagnose "Collect substs" showlen  showsize (collectTreeSubstitutions opts ctxt)
  & diagnose "Collect items"  showsize showsize (collectMenuItems)
  & diagnose "Build menu"     showsize showmenu (buildMenu ctxt)
  where showlen  = show . length
        showsize = show . Set.size
        showmenu (Menu menu) = show (map Set.size (Map.elems menu))
        showctxt _ = "N:o adj.keys: " ++ showlen adjMap ++ ", n:o adj.trees: " ++ showlen adjTrees
        showopts _ = "Pruning: " ++ show opts
        adjMap     = Mono.mapToList (ctxtPrecomputed ctxt)
        adjTrees   = adjMap >>= \(_, ts) → ts
        

diagnose ∷ String → (a → String) → (b → String) → (a → b) → (a → b)
#ifdef DIAGNOSTICS
diagnose title ashow bshow convert input = unsafePerformIO $ do
  printf ">> %s, input: %s\n" title (ashow input)
  time0 <- getCPUTime
  let output = convert input
  printf "   %s, output: %s\n" title (bshow output)
  time1 <- getCPUTime
  let secs :: Float = fromInteger (time1-time0) * 1e-12
  printf "<< %s: %.2f s\n\n" title secs
  return output
#else
diagnose _ _ _ convert = convert
#endif


collectTreeSubstitutions ∷ Prune.PruneOpts → Context → [TTree] → Set (([Tokn], [Node]), ([Tokn], [Node]))
collectTreeSubstitutions opts ctxt oldtrees 
    = Set.fromList [ (linTree ctxt old, linTree ctxt new) | (old, new) ← similarTrees opts ctxt oldtrees ]


collectMenuItems :: Set (([Tokn], [Node]), ([Tokn], [Node])) -> Set (Selection, Selection, [Tokn])
collectMenuItems = Set.map align
    where align ((oldwords, oldnodes), (newwords, newnodes)) = (oldselection, newselection, newwords)
              where (oldselection, newselection) = splitAlignments edits
                    edits = nodeedits <> wordedits
                    -- the node edits are used for finding insertion points:
                    nodeedits = filter (      emptyInterval . fst) $ alignSequences oldnodes newnodes
                    -- the word edits are used for finding which words have changed:
                    wordedits = filter (not . emptyInterval . fst) $ alignSequences oldwords newwords
                    

buildMenu ∷ Context -> Set (Selection, Selection, [Tokn]) → Menu
buildMenu ctxt items
    = Menu $ Map.fromAscListWith Set.union $
      [ (oldselection, Set.singleton (newselection, newlin)) |
        (oldselection, newselection, newwords) <- Set.toAscList items,
        let newlins' = map (Annotated.mkLinearization ctxt) (parseSentence ctxt (Text.unwords newwords)),
        not (null newlins'),
        let newlin = foldl1 Annotated.mergeL newlins'
      ]



-- * LCS

type Edit = (Interval, Interval)

splitAlignments :: [Edit] -> (Selection, Selection)
splitAlignments [] = (mempty, mempty)
splitAlignments ((ij, kl) : edits) = ([ij] <> oldselection, [kl] <> newselection)
    where (oldselection, newselection) = splitAlignments edits

alignSequences :: Eq a => [a] -> [a] -> [Edit]
alignSequences xs ys = cleanEdits $ mergeEdits $ snd $ a Array.! (0,0)
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

type Edit' a = (([a], Int, Int), ([a], Int, Int))

cleanEdits :: [Edit' a] -> [Edit]
cleanEdits eds = [ (Interval (i,j), Interval (k,l)) | ((_,i,j), (_,k,l)) <- eds ]

mergeEdits :: Eq a => [Edit' a] -> [Edit' a]
mergeEdits [] = []
mergeEdits (edit@((xs,_,_), (xs',_,_)) : edits)
    | xs == xs' = mergeEdits edits
    | otherwise = merge edit edits
    where
    merge e [] = [e]
    merge e@((xs0,i,_j), (xs0',i',_j')) (((ys,_k,l), (ys',_k',l')) : edits')
        | ys == ys' = e : mergeEdits edits
        | otherwise = merge ((xs0++ys,i,l), (xs0'++ys',i',l')) edits'
