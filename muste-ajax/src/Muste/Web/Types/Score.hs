module Muste.Web.Types.Score
  ( Score
  , incrScore
  ) where

import Prelude ()
import Muste.Prelude
import Database.SQLite.Simple.FromField
import Database.SQLite.Simple.ToField

newtype Score = Score Int

incrScore ∷ Score → Score
incrScore = undefined

instance Semigroup Score where
  Score a <> Score b = Score $ a + b

instance Monoid Score where
  mempty = Score 0

deriving newtype instance FromJSON  Score
deriving newtype instance ToJSON    Score
deriving newtype instance FromField Score
deriving newtype instance ToField   Score
