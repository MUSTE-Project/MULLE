-- | A scoring system
--
-- Module      : Muste.Web.Config
-- License     : Artistic License 2.0
-- Stability   : experimental
-- Portability : POSIX

{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language RecordWildCards #-}

module Muste.Web.Types.Score
  ( Score(..)
  , addClick
  , setTime
  , valuation
  ) where

import Prelude ()
import Muste.Prelude
import Muste.Prelude.SQL (FromField, ToField)
import qualified Muste.Prelude.SQL as SQL
import qualified GHC.Float as Math
import           GHC.Real ((/))

import Data.Aeson ((.:), (.=))
import qualified Data.Aeson as Aeson
import Data.Binary (Binary(..))

data Score = Score
  -- Does not represent the clicks in the UI, but the time a menu has
  -- been requested corresponding to the times a menu has been chosen.
  { clicks :: Int
  , time   :: NominalDiffTime
  }

instance Binary Score where
  put Score{..} = put clicks <> put (fromEnum time)
  get = Score <$> get <*> (toEnum <$> get)

deriving stock instance Show Score

addClick :: Int -> Score -> Score
addClick n s@Score{..} = s { clicks = clicks + n }

setTime :: NominalDiffTime -> Score -> Score
setTime t s@Score{..} = s { time = t }

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
    $  \b -> Score
    <$> b .: "clicks"
    <*> b .: "time"

-- This feels pretty dirty.  We go via the 'Binary' instance for
-- @(Int, Int)@ using the 'Enum' instance for 'NominalDiffTime' in the
-- process.
instance FromField Score where
  fromField = SQL.fromNullableBlob

instance ToField Score where
  toField = SQL.toBlob


-- This also has an implementation in js:

--   function normalize(x) {
--     return 1 / Math.log(x + 1);
--   }
--   function valuation(score) {
--     return normalize(score.clicks) * normalize(score.time);
--   }
--
-- They must agree.
--
-- FIXME Don't do the above.  Just compute the valuation server-side.
-- | The product of "normalization" the various metrics of a score.
-- The "normalization" ensures that

-- * A positive metric contributes a positive weight
-- * Smaller values are better
-- * Margins near the optimum (zero) are more significant.
valuation :: Score -> Double
valuation Score{..} = normalize clicks * normalize time
  where
  normalize :: Real n => n -> Double
  normalize (realToFrac -> x) = 1 / Math.log (x + 1)
