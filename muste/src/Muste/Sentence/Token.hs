{-# OPTIONS_GHC -Wall -Wno-type-defaults #-}
{-# Language NamedFieldPuns, RecordWildCards, OverloadedStrings
  , DuplicateRecordFields
#-}
module Muste.Sentence.Token
  ( Annotated(Annotated)
  , Unannotated(Unannotated)
  , IsToken(..)
  , annotated
  , unannotated
  , mergeAnnotated
  )
  where

import Prelude hiding (Word)
import Data.Aeson (ToJSON(..), FromJSON(..), (.=), (.:))
import qualified Data.Aeson as Aeson
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import Data.Binary hiding (Word)
import Data.Text.Prettyprint.Doc (Pretty(..))

import Muste.Common.SQL (FromField, ToField)
import qualified Muste.Common.SQL as SQL

import Muste.Sentence.Token.Class (IsToken)
import qualified Muste.Sentence.Token.Class as Token


-- * Annotated words
data Annotated = Annotated
  { concrete ∷ String
  , classes  ∷ Set String
  }

deriving instance Show Annotated
deriving instance Generic Annotated
deriving instance Eq Annotated
deriving instance Ord Annotated
instance Binary Annotated where
instance ToField Annotated where
  toField = SQL.toBlob
instance FromField Annotated where
  fromField = SQL.fromBlob
instance ToJSON Annotated where
  toJSON (Annotated {..}) = Aeson.object
    [ "concrete" .= concrete
    , "classes"  .= classes
    ]
instance FromJSON Annotated where
  parseJSON = Aeson.withObject "token"
    $ \o → Annotated
    <$> o .: "concrete"
    <*> o .: "classes"
instance IsToken Annotated where
  concrete = concrete

annotated ∷ String → [String] → Annotated
annotated c a = Annotated c (Set.fromList a)


-- * Unannotated words

newtype Unannotated = Unannotated { concrete ∷ String }

deriving instance Show Unannotated
deriving instance Eq Unannotated
deriving instance Ord Unannotated
deriving instance Generic Unannotated
instance Binary Unannotated where
instance ToField Unannotated where
  toField = SQL.toBlob
instance FromField Unannotated where
  fromField = SQL.fromBlob
instance ToJSON Unannotated where
  toJSON (Unannotated c) = Aeson.object
    [ "concrete" .= c
    ]
instance FromJSON Unannotated where
  parseJSON = Aeson.withObject "token"
    $ \o → Unannotated
    <$> o .: "concrete"
instance IsToken Unannotated where
  concrete = Muste.Sentence.Token.concrete

instance Pretty Unannotated where
  pretty (Unannotated s) = pretty s

unannotated ∷ String → Unannotated
unannotated = Unannotated

mergeAnnotated ∷ Annotated → Annotated → Annotated
mergeAnnotated (Annotated a0 a1) (Annotated _ b1) = Annotated
  { concrete = a0
  , classes  = Set.union a1 b1
  }
