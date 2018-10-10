{-# OPTIONS_GHC -Wall -Wno-type-defaults #-}
{-# Language NamedFieldPuns, RecordWildCards, OverloadedStrings #-}
module Muste.Sentence.Linearization where

import Prelude ()
import Muste.Prelude
import Muste.Prelude.SQL (FromField, ToField)
import qualified Muste.Prelude.SQL as SQL

import Data.Aeson (ToJSON(..), FromJSON(..))
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import GHC.Generics (Generic)
import Data.Binary hiding (Word)
import Control.Category ((>>>))
import GHC.Exts (IsList(..))
import Data.Typeable (Typeable)
import Data.Text.Prettyprint.Doc (Pretty(..))
import Control.DeepSeq (NFData)
import qualified Data.Text as Text

import Muste.Sentence.Token (IsToken)
import qualified Muste.Sentence.Token as Token

newtype Linearization a = Linearization
  { unLinearization ∷ Vector a }

deriving instance Show a ⇒ Show (Linearization a)
deriving instance FromJSON a ⇒ FromJSON (Linearization a)
deriving instance ToJSON a ⇒ ToJSON (Linearization a)
deriving instance Eq a ⇒ Eq (Linearization a)
deriving instance Ord a ⇒ Ord (Linearization a)
deriving instance Generic a ⇒ Generic (Linearization a)
instance (Generic a, NFData a) ⇒ NFData (Linearization a) where

-- There is no 'Binary' instance for 'Vector', so we go via '[]'.
instance Binary a ⇒ Binary (Linearization a) where
  put = put @[a] . Vector.toList . unLinearization
  get = Linearization . Vector.fromList <$> get @[a]

instance (Binary a, Typeable a) ⇒ ToField (Linearization a) where
  toField = SQL.toBlob

instance (Binary a, Typeable a) ⇒ FromField (Linearization a) where
  fromField = SQL.fromBlob

instance IsList (Linearization a) where
  type Item (Linearization a) = a
  fromList = Vector.fromList >>> Linearization
  toList = unLinearization >>> Vector.toList

instance IsToken a ⇒ Pretty (Linearization a) where
  pretty = pretty . stringRep

-- FIXME change name to @textRep@
stringRep ∷ IsToken a ⇒ Linearization a → Text
stringRep
  =   toList
  >>> fmap Token.concrete
  >>> Text.unwords
