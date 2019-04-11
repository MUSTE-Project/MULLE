{-# OPTIONS_GHC -Wall -Wno-type-defaults #-}
{-# Language
 DeriveGeneric,
 GeneralizedNewtypeDeriving,
 NamedFieldPuns,
 OverloadedStrings,
 RecordWildCards,
 ScopedTypeVariables,
 StandaloneDeriving,
 TypeApplications,
 TypeFamilies
#-}

module Muste.Sentence.Linearization where

import Control.Category ((>>>))
import Control.DeepSeq (NFData)
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Muste.Prelude.SQL (toBlob, fromBlob)
import Database.SQLite.Simple.ToField (ToField(toField))
import Database.SQLite.Simple.FromField (FromField(fromField))

import Data.Aeson (ToJSON, FromJSON)
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Binary hiding (Word)
import qualified Data.Text as Text
import Data.Text (Text)
import Data.Text.Prettyprint.Doc (Pretty(..))
import GHC.Exts (IsList(fromList, toList, Item))

import Muste.Sentence.Token (IsToken)
import qualified Muste.Sentence.Token as Token


newtype Linearization a = Linearization
  { unLinearization :: Vector a }

deriving instance Show a => Show (Linearization a)
deriving instance FromJSON a => FromJSON (Linearization a)
deriving instance ToJSON a => ToJSON (Linearization a)
deriving instance Eq a => Eq (Linearization a)
deriving instance Ord a => Ord (Linearization a)
deriving instance Generic a => Generic (Linearization a)
instance (Generic a, NFData a) => NFData (Linearization a) where

-- There is no 'Binary' instance for 'Vector', so we go via '[]'.
instance Binary a => Binary (Linearization a) where
  put = put @[a] . Vector.toList . unLinearization
  get = Linearization . Vector.fromList <$> get @[a]

instance (Binary a, Typeable a) => ToField (Linearization a) where
  toField = toBlob

instance (Binary a, Typeable a) => FromField (Linearization a) where
  fromField = fromBlob

instance IsList (Linearization a) where
  type Item (Linearization a) = a
  fromList = Vector.fromList >>> Linearization
  toList = unLinearization >>> Vector.toList

instance IsToken a => Pretty (Linearization a) where
  pretty = pretty . stringRep

-- FIXME change name to @textRep@
stringRep :: IsToken a => Linearization a -> Text
stringRep
  =   toList
  >>> fmap Token.concrete
  >>> Text.unwords
