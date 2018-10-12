{-# OPTIONS_GHC -Wall -Wno-orphans #-}
-- | Adjunction trees
--
-- Interfacint with 'AdjunctionTrees' is done using the interface for
-- monomorphic map containers.
module Muste.AdjunctionTrees.Internal
    ( AdjunctionTrees(AdjunctionTrees)
    , AdjKey, AdjTree
    ) where

import Prelude ()
import Muste.Prelude
import qualified Data.Containers      as Mono
import Data.MonoTraversable
import qualified Data.Map.Strict      as M
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet
import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import qualified Data.Binary as Binary

import Muste.Tree

instance Binary a ⇒ Binary (MultiSet a) where
  get = MultiSet.fromOccurMap <$> Binary.get
  put = Binary.put . MultiSet.toMap

type AdjKey = (Category, MultiSet Category)
type AdjTree = (AdjKey, TTree)

-- TODO: add (multi)set of the functions in the Adjtree

-- | @AdjunctionTrees@ really is a map from a @Category@ to a set of
-- trees that have this category.
newtype AdjunctionTrees
  = AdjunctionTrees (M.Map AdjKey [TTree])
  deriving (Show, MonoFunctor, Generic, NFData, Binary)

type instance Element AdjunctionTrees = [TTree]

instance MonoFoldable AdjunctionTrees where
  ofoldl'    f a (AdjunctionTrees m) = ofoldl' f a m
  ofoldr     f a (AdjunctionTrees m) = ofoldr f a m
  ofoldMap   f (AdjunctionTrees m)   = ofoldMap f m
  ofoldr1Ex  f (AdjunctionTrees m)   = ofoldr1Ex f m
  ofoldl1Ex' f (AdjunctionTrees m)   = ofoldl1Ex' f m

instance MonoTraversable AdjunctionTrees where
  otraverse f (AdjunctionTrees m) = AdjunctionTrees <$> otraverse f m

deriving instance Semigroup AdjunctionTrees

deriving instance Monoid AdjunctionTrees

instance GrowingAppend AdjunctionTrees where

instance Mono.SetContainer AdjunctionTrees where
  type ContainerKey AdjunctionTrees = (Category, MultiSet Category)
  member k     (AdjunctionTrees m) = Mono.member k m
  notMember k  (AdjunctionTrees m) = Mono.notMember k m
  union        (AdjunctionTrees a) (AdjunctionTrees b) = AdjunctionTrees $ a `Mono.union` b
  intersection (AdjunctionTrees a) (AdjunctionTrees b) = AdjunctionTrees $ a `Mono.intersection` b
  difference   (AdjunctionTrees a) (AdjunctionTrees b) = AdjunctionTrees $ a `Mono.difference` b
  keys         (AdjunctionTrees m) = Mono.keys m

instance Mono.IsMap AdjunctionTrees where
  type MapValue AdjunctionTrees = [TTree]
  lookup c       (AdjunctionTrees m) = Mono.lookup c m
  singletonMap c t                   = AdjunctionTrees $ Mono.singletonMap c t
  mapFromList as                     = AdjunctionTrees $ Mono.mapFromList as
  insertMap k vs (AdjunctionTrees m) = AdjunctionTrees $ Mono.insertMap k vs m
  deleteMap k    (AdjunctionTrees m) = AdjunctionTrees $ Mono.deleteMap k m
  mapToList      (AdjunctionTrees m) = Mono.mapToList m
