{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language
 DeriveAnyClass,
 DeriveGeneric,
 DerivingStrategies,
 GeneralizedNewtypeDeriving,
 NamedFieldPuns,
 OverloadedStrings,
 RecordWildCards,
 StandaloneDeriving,
 TypeApplications
#-}

module Muste.Sentence.Language
  (Language(Language), Grammar(Grammar))
  where

import Database.SQLite.Simple.ToField (ToField)
import Database.SQLite.Simple.FromField (FromField)

import GHC.Generics (Generic)
import Data.Aeson ((.=), (.:), FromJSON, ToJSON)
import qualified Data.Aeson as Aeson
import Data.Binary (Binary)
import Data.String (IsString(fromString))
import Data.Text (Text)


newtype Grammar = Grammar Text

deriving stock   instance Show      Grammar
deriving newtype instance Eq        Grammar
deriving newtype instance Ord       Grammar
deriving newtype instance FromJSON  Grammar
deriving newtype instance ToJSON    Grammar
deriving stock   instance Generic   Grammar
deriving newtype instance Binary    Grammar
deriving newtype instance FromField Grammar
deriving newtype instance ToField   Grammar
deriving newtype instance IsString  Grammar

data Language = Language
  -- NB This field is not in use.
  { grammar  :: Grammar
  , lang     :: Text
  }
                             
deriving stock instance Show Language
deriving stock instance Eq   Language
deriving stock instance Ord  Language

-- | The implementation is a bit hacky, we just use the read instance
-- for pairs to be able to parse a 'Language'.  So the language must
-- be given as:
--
--   "(\"grammar\", \"lang\")"
--
-- Note the gratiutious double-quotes.  Not exactly the most
-- elegant...
instance IsString Language where
  fromString s = Language (fromString g) (fromString l)
    where
    (g, l) = read @(String, String) s

instance ToJSON Language where
  toJSON (Language {..}) = Aeson.object
    [ "grammar"  .= grammar
    , "language" .= lang
    ]

instance FromJSON Language where
  parseJSON = Aeson.withObject "word"
    $ \o -> Language
    <$> o .: "grammar"
    <*> o .: "language"

deriving stock    instance Generic Language
deriving anyclass instance Binary  Language
