{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
{-# Language OverloadedStrings, CPP, RecordWildCards #-}
module Muste.Menu.Internal
  ( Menu
  , getMenu
  , CostTree
  , lin
  , getMenuFromStringRep
  ) where

import Data.Maybe
import Data.List
-- FIXME I think we might need to consider switching to strict maps.
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy   as Map
import Data.Set (Set)
import qualified Data.Set        as Set
import Data.Aeson hiding (pairs)
import Data.Aeson.Types (Parser)
import qualified Data.Containers as Mono
import Data.MonoTraversable
import Data.Function (on)
import Control.Category ((>>>))
#if !(MIN_VERSION_base(4,11,0))
import Data.Semigroup (Semigroup((<>)))
#endif
import Data.Text.Prettyprint.Doc (Pretty(..), Doc, (<+>), brackets)
import qualified Data.Text.Prettyprint.Doc as Doc

import Muste.Common
import Muste.Tree
import qualified Muste.Prune as Prune
import Muste.Linearization
import qualified Muste.Linearization.Internal as Linearization
import Muste.Selection (Selection)
import qualified Muste.Selection as Selection
import qualified Muste.Grammar.Internal as Grammar

-- | A 'CostTree' is a tree associated with it's linearization and a
-- "cost".  The cost is with reference to some "base tree".  The only
-- way to construct 'CostTree's[^1] is via 'getCleanMenu' which takes
-- a 'TTree'.  The cost is in reference to that tree.
--
-- [^1]: Here's to hoping this documentation will be kept up-to-date.
data CostTree = CostTree
  { cost           ∷ Int
  , lin            ∷ Linearization
  , ctIsInsertion   ∷ Bool
  -- TODO Add this:
  -- , changedWords   ∷ Selection
  } deriving (Show,Eq)

instance Pretty CostTree where
  pretty (CostTree { .. }) = ins <> pretty lin <+> brackets (pretty cost)
    where
    ins = if ctIsInsertion then pretty @String "INS: " else mempty

instance FromJSON CostTree where
  parseJSON = withObject "CostTree" $ \v -> CostTree
    <$> v .: "cost"
    <*> v .: "lin"
    <*> v .: "insertion"

instance ToJSON CostTree where
  toJSON (CostTree score lin repl) = object
    [ "score"       .= score
    , "lin"         .= lin
    , "insertion"   .= repl
    ]

-- | @'getPrunedSuggestions' ctxt tree@ finds all trees similar to
-- @tree@ in @ctxt@.  Return a mapping from 'Path''s to the
-- @CostTree@'s you get when you replace one of the valid trees into
-- that given position along with the "cost" of doing so.
--
-- These cost trees are supposed to be grouped somehow, I don't quite
-- remember what the idea with this is, but currently the outermost
-- list is always a singleton.
getPrunedSuggestions :: Context -> TTree -> Menu
getPrunedSuggestions ctxt tree = menu
  where
  toSel ∷ Path → Selection
  toSel p = selectionFromPath p (Linearization.linearizeTree ctxt tree)
  pathMap ∷ Map Path (Mono.MapValue Menu)
  pathMap = go `Map.map` replaceTrees tree
  replaceTrees :: TTree -> Map Path (Set (Prune.SimTree, TTree))
  replaceTrees
    = Prune.replaceTrees (ctxtGrammar ctxt) (ctxtPrecomputed ctxt)
  go ∷ Set (Prune.SimTree, TTree) -> Mono.MapValue Menu
  go = costTrees ctxt tree
  menu = Menu $ Map.mapKeysWith (mappend @[CostTree]) toSel pathMap

-- | Creates a 'CostTree' from a tree and its cost.  Since the cost is
-- already calculated, it basically just linearizes the tree.
costTrees
  :: Context       -- ^ Context of the tree
  -> TTree         -- ^ The original tree
  -> Set (Prune.SimTree, TTree)
  -> Mono.MapValue Menu
costTrees ctxt t
  =   Set.toList
  -- First make a list of provisional 'CostTree's.
  >>> map go
  -- Then smash them together based on their linearization.
  >>> regroup
  where
  go ∷ (Prune.SimTree, TTree) → CostTree
  go (s, u) = costTree ctxt t s u

-- | After we've found all replacement trees we want to regroup them,
-- so that all the `TTree`s that have the same linearization gets
-- grouped into one set.  Currently I'm assuming that there is a
-- functional dependency @TTree → SimTree@ in the input set.  I.e.:
--
--     @∀ (sim, t) (sim', t') ∷ (SimTree, TTree) . t ~ t' ⇒ sim ~ sim'@
regroup ∷ [CostTree] → [CostTree]
regroup = groupOnSingle lin

-- | Creates a 'CostTree' from a tree and its cost.  Since the cost is
-- already calculated, it basically just linearizes the tree.
costTree
  :: Context       -- ^ Context of the tree
  -> TTree         -- ^ The original tree
  -> Prune.SimTree -- ^ Information regarding what the tree is replacing
  -> TTree         -- ^ The replacement tree
  -> CostTree
costTree ctxt s (cost, r, _, _) t
  = CostTree cost (Linearization.linearizeTree ctxt t) ins
  where
  ins :: Bool
  ins = isInsertion ctxt s r

-- | @'isInsertion' ctxt p s r@ determines if the subtree @r@ is to be
-- considered an "insertion" into the tree @s@.
isInsertion :: Context -> TTree -> TTree -> Bool
isInsertion ctxt s r = isJust $ Linearization.isInsertion ctxt s r

-- | Very similar to 'coverNodes', but in stead of saving the paths we
-- save the index of the 'Linearization'.
selectionFromPath ∷ Path → Linearization → Selection
selectionFromPath p
  =   otoList
  >>> fmap Linearization.ltpath
  >>> enumerate
  >>> filter (snd >>> isPrefixOf p)
  >>> fmap fst
  >>> Selection.fromList

filterCostTrees :: Menu -> Menu
filterCostTrees = removeFree >>> sortByCost >>> filterEmpty
  where
  removeFree  :: Menu -> Menu
  removeFree  = omap $ filter $ (/= 0) . cost
  filterEmpty :: Menu -> Menu
  filterEmpty = monofilter $ not . null
  sortByCost  :: Menu -> Menu
  sortByCost  = omap $ sortBy (compare `on` cost)

-- TODO This call is quite heavy.
getCleanMenu :: Context -> TTree -> Menu
getCleanMenu context tree
  = filterCostTrees
  $ getPrunedSuggestions context tree

-- | Generate a 'Menu' from a linearization.
getMenu ∷ Context → Linearization → Menu
getMenu ctxt
  =   Linearization.disambiguate ctxt
  >>> foldMap (getCleanMenu ctxt)

-- If we had an ordering on `CostTree`s we could also use `Set` here
-- in stead of `[]`.
-- | A 'Menu' maps 'Selection's to 'CostTree's.
newtype Menu = Menu (Map Selection [CostTree]) deriving (Show)

instance Pretty Menu where
  pretty (Menu mp) = Doc.vsep $ map p $ Map.toList $ mp
    where
    p ∷ ∀ a . (Selection, [CostTree]) → Doc.Doc a
    p (p, cs) = Doc.nest 2 $ Doc.vsep $ pretty p : map prettyCt cs
    prettyCt ∷ CostTree → Doc a
    prettyCt = pretty . lin

instance FromJSON Menu where
  -- parseJSON = withObject "menu" (parseJSON' . Object)
  parseJSON = parseJSON'
    where
    parseJSON' ∷ Value → Parser Menu
    parseJSON'
      = fmap Mono.mapFromList
      . parseJSON @[(Selection, [CostTree])]

instance ToJSON Menu where
  -- toJSON m = object [ "menu" .= toJSON' m ]
  toJSON = toJSON'
    where
    toJSON' ∷ Menu → Value
    toJSON' = toJSON @[(Selection, [CostTree])] . Mono.mapToList

instance Semigroup Menu where
  -- | When 'Menu's are combined, if they share a key, then the
  -- '[CostTree]' they map to are 'mappend'ed together.
  Menu a <> Menu b = Menu $ Map.unionWith (mappend @[CostTree]) a b

instance Monoid Menu where
  mempty = Menu mempty
  mappend = (<>)

deriving instance MonoFunctor Menu

type instance Element Menu = [CostTree]

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
  type ContainerKey Menu = Selection
  member k     (Menu m) = Mono.member k m
  notMember k  (Menu m) = Mono.notMember k m
  union        (Menu a) (Menu b) = Menu $ a `Mono.union` b
  intersection (Menu a) (Menu b) = Menu $ a `Mono.intersection` b
  difference   (Menu a) (Menu b) = Menu $ a `Mono.difference` b
  keys         (Menu m) = Mono.keys m

instance Mono.IsMap Menu where
  type MapValue Menu      = [CostTree]
  lookup c       (Menu m) = Mono.lookup c m
  singletonMap c t        = Menu $ Mono.singletonMap c t
  mapFromList as          = Menu $ Mono.mapFromList as
  insertMap k vs (Menu m) = Menu $ Mono.insertMap k vs m
  deleteMap k    (Menu m) = Menu $ Mono.deleteMap k m
  mapToList      (Menu m) = Mono.mapToList m

-- | Probably an inefficient implementation.  See my question at
-- somewhere down the thread here:
-- <https://github.com/snoyberg/mono-traversable/issues/15>
monofilter :: Mono.IsMap map => (Mono.MapValue map -> Bool) -> map -> map
monofilter p = Mono.mapFromList . filter (p . snd) . Mono.mapToList

getMenuFromStringRep ∷ Context → String → Menu
getMenuFromStringRep ctxt = foldMap (getMenu ctxt) . parseLin ctxt

parseLin ∷ Context → String → Set Linearization
parseLin ctxt = parseTree >>> map mkL >>> Set.fromList
  where
  grammar = ctxtGrammar ctxt
  parseTree ∷ String → [TTree]
  parseTree = Grammar.parseSentence grammar (Linearization.ctxtLang ctxt)
  mkL ∷ TTree → Linearization
  mkL = Linearization.mkLinSimpl ctxt
