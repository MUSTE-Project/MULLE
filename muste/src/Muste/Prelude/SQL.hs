{-# OPTIONS_GHC -Wall #-}
-- | I got a bit sick of having to import 3 different modules to use
-- the SQL-backend, hence this module.
module Muste.Prelude.SQL
  ( SQL.FromField(..)
  , SQL.ToField(..)
  , SQL.fieldData
  , SQL.returnError
  , SQL.SQLData(..)
  , SQL.ResultError(..)
  , fromBlob
  , toBlob
  , fromNullableBlob
  , SQL.FromRow(..)
  , SQL.ToRow(..)
  , Nullable(..)
  , SQL.SQLError(..)
  , SQL.Error(..)
  , SQL.query
  , SQL.query_
  , SQL.execute
  , SQL.executeMany
  , SQL.open
  , SQL.Connection(Connection)
  , SQL.Query
  , SQL.withConnection
  , SQL.sql
  , SQL.Only(Only)
  , SQL.fromOnly
  , SQL.setTrace
  , ToNamed(..)
  , SQL.NamedParam(..)
  , SQL.queryNamed
  , SQL.executeNamed
  ) where

import Prelude ()
import Muste.Prelude
import Muste.Prelude.Extra

import qualified Database.SQLite.Simple           as SQL
import qualified Database.SQLite.Simple.Ok        as SQL
import qualified Database.SQLite.Simple.ToField   as SQL
import qualified Database.SQLite.Simple.FromField as SQL
import qualified Database.SQLite.Simple.QQ        as SQL
import Data.Binary (Binary)
import Data.Typeable (Typeable)
import Data.ByteString (ByteString)

fromBlob ∷ Typeable b ⇒ Binary b ⇒ SQL.Field → SQL.Ok b
fromBlob fld = case SQL.fieldData fld of
  SQL.SQLBlob t -> pure $ binaryFromText t
  _ -> SQL.returnError SQL.ConversionFailed fld mempty

toBlob ∷ ∀ b . Binary b ⇒ b → SQL.SQLData
toBlob = SQL.SQLBlob . binaryToText @b @ByteString

-- | Safe conversion of blob columns that may be null.
fromNullableBlob ∷ Typeable b ⇒ Binary b ⇒ Monoid b ⇒ SQL.Field → SQL.Ok b
fromNullableBlob fld = case SQL.fieldData fld of
  SQL.SQLBlob t -> pure $ binaryFromText t
  SQL.SQLNull → pure mempty
  _ -> SQL.returnError SQL.ConversionFailed fld mempty

newtype Nullable a = Nullable { runNullable ∷ a }

deriving stock   instance Show a ⇒ Show (Nullable a)
deriving newtype instance Binary a ⇒ Binary (Nullable a)
instance (Monoid a, Binary a, Typeable a) ⇒ SQL.FromField (Nullable a) where
  fromField = fmap Nullable . fromNullableBlob
instance Binary a ⇒ SQL.ToField (Nullable a) where
  toField = toBlob

-- We could consider making 'ToRow' a super-class but it's not
-- strictly necessary.
class ToNamed a where
  toNamed ∷ a → [SQL.NamedParam]
