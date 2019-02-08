-- | Generic derivation of 'FromRow' and 'ToRow' for product-types.
--
-- A PR has been submitted against upstream to get this functionality
-- into the `sqlite-simple`.[1]
--
-- [1]: https://github.com/nurpax/sqlite-simple/pull/69
{-# OPTIONS_GHC -Wall #-}
{-# Language TypeOperators #-}
module Database.SQLite.Simple.FromRow.Generic
  ( GFromRow(..)
  , GToRow(..)
  , genericFromRow
  , genericToRow
  ) where

import Database.SQLite.Simple
import Database.SQLite.Simple.FromRow
import Database.SQLite.Simple.FromField
import Database.SQLite.Simple.ToField
import GHC.Generics

class GFromRow f where
  gfromRow :: RowParser (f a)

instance GFromRow (U1 :: * -> *) where
  gfromRow = pure U1

instance FromField a => GFromRow (K1 i a :: * -> *) where
  gfromRow = K1 <$> field

instance GFromRow a => GFromRow (M1 i c a :: * -> *) where
  gfromRow = M1 <$> gfromRow

instance (GFromRow a, GFromRow b) => GFromRow (a :*: b :: * -> *) where
  gfromRow = (:*:) <$> gfromRow <*> gfromRow

genericFromRow
  :: forall g . Generic g
  => GFromRow (Rep g)
  => RowParser g
genericFromRow = to <$> gfromRow

class GToRow f where
  gtoRow :: (f a) -> [SQLData]

instance GToRow (U1 :: * -> *) where
  gtoRow U1 = toRow ()

instance ToField a => GToRow (K1 i a :: * -> *) where
  gtoRow (K1 a) = pure $ toField a

instance (GToRow a, GToRow b) => GToRow (a :*: b :: * -> *) where
  gtoRow (a :*: b) = gtoRow a <> gtoRow b

instance GToRow a => GToRow (M1 i c a :: * -> *) where
  gtoRow (M1 a) = gtoRow a

genericToRow
  :: forall g . Generic g
  => GToRow (Rep g)
  => g -> [SQLData]
genericToRow g = gtoRow $ from g
