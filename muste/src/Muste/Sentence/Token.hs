{-# OPTIONS_GHC -Wall -Wno-type-defaults #-}
{-# Language NamedFieldPuns, RecordWildCards, OverloadedStrings
  , DuplicateRecordFields
#-}
module Muste.Sentence.Token
  ( Unambiguous
  , Ambiguous
  , IsToken(..)
  , unambiguous
  , ambiguous
  , mergeUnambiguous
  )
  where

import Prelude hiding (Word)
import Data.Aeson (ToJSON(..), FromJSON(..), (.=), (.:))
import qualified Data.Aeson as Aeson
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import Data.Binary hiding (Word)

import Muste.Common.SQL (FromField, ToField)
import qualified Muste.Common.SQL as SQL

import Muste.Sentence.Token.Class (IsToken)
import qualified Muste.Sentence.Token.Class as Token


-- * Unambiguous words
data Unambiguous = Unambiguous
  { concrete ∷ String
  , classes  ∷ Set String
  }

deriving instance Show Unambiguous
deriving instance Generic Unambiguous
instance Binary Unambiguous where
instance ToField Unambiguous where
  toField = SQL.toBlob
instance FromField Unambiguous where
  fromField = SQL.fromBlob
instance ToJSON Unambiguous where
  toJSON (Unambiguous {..}) = Aeson.object
    [ "concrete" .= concrete
    , "classes"  .= classes
    ]
instance FromJSON Unambiguous where
  parseJSON = Aeson.withObject "token"
    $ \o → Unambiguous
    <$> o .: "concrete"
    <*> o .: "classes"
instance IsToken Unambiguous where
  concrete = concrete

unambiguous ∷ String → [String] → Unambiguous
unambiguous c a = Unambiguous c (Set.fromList a)


-- * Ambiguous words

newtype Ambiguous = Ambiguous { concrete ∷ String }

deriving instance Show Ambiguous
deriving instance Eq Ambiguous
deriving instance Ord Ambiguous
deriving instance Generic Ambiguous
instance Binary Ambiguous where
instance ToField Ambiguous where
  toField = SQL.toBlob
instance FromField Ambiguous where
  fromField = SQL.fromBlob
instance ToJSON Ambiguous where
  toJSON (Ambiguous c) = Aeson.object
    [ "concrete" .= c
    ]
instance FromJSON Ambiguous where
  parseJSON = Aeson.withObject "token"
    $ \o → Ambiguous
    <$> o .: "concrete"
instance IsToken Ambiguous where
  concrete = Muste.Sentence.Token.concrete

ambiguous ∷ String → Ambiguous
ambiguous = Ambiguous

mergeUnambiguous ∷ Unambiguous → Unambiguous → Unambiguous
mergeUnambiguous (Unambiguous a0 a1) (Unambiguous _ b1) = Unambiguous
  { concrete = a0
  , classes  = Set.union a1 b1
  }
