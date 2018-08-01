{-# Language
    OverloadedStrings
  , StandaloneDeriving
  , GeneralizedNewtypeDeriving
  , TypeFamilies
#-}
module Muste.Menu
  ( Menu
  , getCleanMenu
  , CostTree
  ) where

import Data.List
-- FIXME I think we might need to consider switching to strict maps.
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy   as Map
import Data.Set (Set)
import qualified Data.Set        as Set
import Data.Aeson
import qualified Data.Text as Text
import qualified Data.Containers as Mono
import Data.MonoTraversable
import Data.Function (on)
import Control.Category ((>>>))

import Muste.Tree
import qualified Muste.Prune as Prune
import Muste.Linearization
import qualified Muste.Linearization.Internal as Linearization
  ( linearizeTree
  )

-- | A 'CostTree' is a tree associated with it's linearization and a
-- "cost".  The cost is with reference to some "base tree".  The only
-- way to construct 'CostTree's[^1] is via 'getCleanMenu' which takes
-- a 'TTree'.  The cost is in reference to that tree.
--
-- [^1]: Here's to hoping this documentation will be kept up-to-date.
data CostTree = CostTree
  { cost :: Int
  , _lin :: Linearization
  , _tree :: TTree
  } deriving (Show,Eq)

instance FromJSON CostTree where
  parseJSON = withObject "CostTree" $ \v -> CostTree
    <$> v .: "cost"
    <*> v .: "lin"
    <*> v .: "tree"

instance ToJSON CostTree where
  toJSON (CostTree score lin tree) = object
    [ "score" .= score
    , "lin"   .= lin
    , "tree"  .= tree
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
getPrunedSuggestions ctxt tree = Menu $ go `Map.mapWithKey` Prune.replaceTrees (ctxtGrammar ctxt) (ctxtPrecomputed ctxt) tree
  where
  go :: Path -> Set (Int, TTree) -> Mono.MapValue Menu
  go path = map (uncurry (costTree ctxt)) . Set.toList

-- | Creates a 'CostTree' from a tree and it's cost.  Since the cost
-- is already calculated, it basically just linearizes the tree.
costTree :: Context -> Int -> TTree -> CostTree
costTree ctxt cost fullTree
  = CostTree cost (Linearization.linearizeTree ctxt fullTree) fullTree

filterCostTrees :: Menu -> Menu
filterCostTrees = removeFree >>> sortByCost >>> filterEmpty
  where
  removeFree  :: Menu -> Menu
  removeFree  = omap $ filter $ (/= 0) . cost
  filterEmpty :: Menu -> Menu
  filterEmpty = monofilter $ not . null
  sortByCost  :: Menu -> Menu
  sortByCost  = omap $ sortBy (compare `on` cost)

getCleanMenu :: Context -> TTree -> Menu
getCleanMenu context tree
  = filterCostTrees
  $ getPrunedSuggestions context tree

-- If we had an ordering on `CostTree`s we could also use `Set` here
-- in stead of `[]`.
-- | A 'Menu' maps paths to 'CostTree's.
newtype Menu = Menu (Map Path [CostTree]) deriving (Show)

instance FromJSON Menu where
  parseJSON = withObject "CostTree" $ \v -> Menu
    <$> v .: "menu"

instance ToJSON Menu where
    toJSON (Menu map) =
      object [ (Text.pack $ show k) .= (Map.!) map  k | k <- Map.keys map]

deriving instance Semigroup Menu

deriving instance Monoid Menu

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
  type ContainerKey Menu = Path
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
