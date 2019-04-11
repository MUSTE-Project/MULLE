{-# OPTIONS_GHC -Wall #-}
{-# Language
 DeriveGeneric,
 GeneralizedNewtypeDeriving,
 StandaloneDeriving,
 TypeFamilies
#-}

-- | A 'Set' with a dfferent 'Ord' instance.
module Muste.Selection
    ( Interval(Interval, runInterval)
    , Selection(Selection, runSelection)
    ) where

import Control.Category ((>>>))
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)

import GHC.Exts (IsList(fromList, toList, Item))
import qualified Data.List as List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text.Prettyprint.Doc (Pretty(pretty))
import Data.Aeson (ToJSONKey(toJSONKey), ToJSONKeyFunction(ToJSONKeyValue),
                   FromJSONKey(fromJSONKey), FromJSONKeyFunction(FromJSONKeyValue),
                   FromJSON, ToJSON(toJSON, toEncoding), parseJSON)


newtype Interval = Interval { runInterval :: (Int, Int) }

deriving instance ToJSONKey Interval
deriving instance FromJSONKey Interval
deriving instance ToJSON Interval
deriving instance FromJSON Interval
deriving instance Show Interval
deriving instance Eq Interval
deriving instance Ord Interval
deriving instance Read Interval
deriving instance Generic Interval
instance NFData Interval where

sizeInterval :: Interval -> Int
sizeInterval (Interval (i, j)) = 100 * (j - i) + 1
-- The added small constant is so that empty intervals are also counted.
-- With this, the selection {2-3} will come before {2-2,2-3}.


newtype Selection = Selection { runSelection :: Set Interval }

deriving instance Read Selection
instance ToJSONKey Selection where
    toJSONKey = ToJSONKeyValue toJSON toEncoding
instance FromJSONKey Selection where
    fromJSONKey = FromJSONKeyValue parseJSON
deriving instance Show Selection
deriving instance ToJSON Selection
deriving instance FromJSON Selection
instance IsList Selection where
  type Item Selection = Interval
  fromList = Selection . Set.fromList
  toList = Set.toList . runSelection
deriving instance Eq Selection
instance Ord Selection where
  a `compare` b = case size a `compare` size b of
    EQ -> runSelection a `compare` runSelection b
    x  -> x
    where
    size :: Selection -> Int
    size = runSelection >>> Set.map sizeInterval >>> sum
deriving instance Generic Selection
instance NFData Selection where

deriving instance Semigroup Selection
deriving instance Monoid Selection

instance Pretty Selection where
  pretty sel = pretty $ showSelection sel

showSelection :: Selection -> String
showSelection sel = "{" ++ List.intercalate "," [ show i ++ "-" ++ show j |
                                             Interval (i,j) <- Set.toList (runSelection sel)]
                    ++ "}"
