{-# OPTIONS_GHC -Wall #-}

module Muste.Prelude.SQL
  ( fromBlob
  , toBlob
  , fromNullableBlob
  ) where

import Prelude ()
import Muste.Prelude
import Muste.Prelude.Extra

import qualified Database.SQLite.Simple           as SQL
import qualified Database.SQLite.Simple.Ok        as SQL
import qualified Database.SQLite.Simple.FromField as SQL
import Data.Binary (Binary)
import Data.Typeable (Typeable)

fromBlob :: Typeable b => Binary b => SQL.Field -> SQL.Ok b
fromBlob fld = case SQL.fieldData fld of
  SQL.SQLBlob t -> pure $ binaryFromText t
  _ -> SQL.returnError SQL.ConversionFailed fld mempty

toBlob :: Binary b => b -> SQL.SQLData
toBlob = SQL.SQLBlob . binaryToText

-- | Safe conversion of blob columns that may be null.
fromNullableBlob :: Typeable b => Binary b => Monoid b => SQL.Field -> SQL.Ok b
fromNullableBlob fld = case SQL.fieldData fld of
  SQL.SQLBlob t -> pure $ binaryFromText t
  SQL.SQLNull -> pure mempty
  _ -> SQL.returnError SQL.ConversionFailed fld mempty
