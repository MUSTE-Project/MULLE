{-# Language RecordWildCards, DeriveAnyClass #-}
module Muste.Web.Types.Score
  ( Score(..)
  , addClick
  ) where

import Prelude ()
import Muste.Prelude
import Database.SQLite.Simple.FromField
import Database.SQLite.Simple.ToField
import Data.Time (NominalDiffTime)
import Data.Aeson ((.:), (.=), (.:?))
import qualified Data.Aeson as Aeson
import Muste.Common.SQL (FromField, ToField)
import qualified Muste.Common.SQL as SQL

data Score = Score
  -- Does not represent the clicks in the UI, but the time a menu has
  -- been requested corresponding to the times a menu has been chosen.
  { clicks ∷ Int
  , time   ∷ NominalDiffTime
  }

addClick ∷ Score → Score
addClick s@Score{..} = s { clicks = succ clicks }

instance Semigroup Score where
  a <> b
    = Score
    { clicks = clicks a + clicks b
    , time   = time a   + time b
    }

instance Monoid Score where
  mempty = Score 0 0


instance ToJSON Score where
  toJSON Score{..} = Aeson.object
    [ "clicks" .= clicks
    , "time"   .= time
    ]

instance FromJSON Score where
  parseJSON = Aeson.withObject "score"
    $  \b → Score
    <$> b .: "clicks"
    <*> b .: "time"

-- This feels pretty dirty.  We go via the 'Binary' instance for
-- @(Int, Int)@ using the 'Enum' instance for 'NominalDiffTime' in the
-- process.
instance FromField Score where
  fromField = fmap conv <$> SQL.fromBlob @(Int, Int)
    where
    conv ∷ (Int, Int) → Score
    conv (a, b) = Score a (toEnum b)

instance ToField Score where
  toField = SQL.toBlob @(Int, Int) . conv
    where
    conv ∷ Score → (Int, Int)
    conv Score{..} = (clicks, fromEnum time)
