module Muste.Web.Types where

import Prelude ()
import Muste.Prelude
import Database.SQLite.Simple.FromField
import Database.SQLite.Simple.ToField

newtype Score = Score Int

deriving newtype instance Num       Score
deriving newtype instance Enum      Score
deriving newtype instance FromJSON  Score
deriving newtype instance ToJSON    Score
deriving newtype instance FromField Score
deriving newtype instance ToField   Score
