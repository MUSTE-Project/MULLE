-- | I got a bit sick of having to import 3 different modules to use
-- the SQL-backend, hence this module.
module Muste.Common.SQL
  ( SQL.FromField(..)
  , SQL.ToField(..)
  , SQL.fieldData
  , SQL.returnError
  , SQL.SQLData(..)
  , SQL.ResultError(..)
  , fromBlob
  , toBlob
  ) where

import qualified Database.SQLite.Simple           as SQL
import qualified Database.SQLite.Simple.Ok        as SQL
import qualified Database.SQLite.Simple.ToField   as SQL
import qualified Database.SQLite.Simple.FromField as SQL
import Data.Binary (Binary)
import Data.Typeable (Typeable)
import Data.ByteString (ByteString)

import Muste.Common (binaryToText, binaryFromText)

fromBlob ∷ Typeable b ⇒ Binary b ⇒ SQL.Field → SQL.Ok b
fromBlob fld = case SQL.fieldData fld of
    SQL.SQLBlob t -> pure $ binaryFromText t
    _ -> SQL.returnError SQL.ConversionFailed fld mempty

toBlob ∷ ∀ b . Binary b ⇒ b → SQL.SQLData
toBlob = SQL.SQLBlob . binaryToText @b @ByteString
