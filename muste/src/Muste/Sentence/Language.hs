{-# OPTIONS_GHC -Wall -Wno-type-defaults #-}
{-# Language NamedFieldPuns, RecordWildCards, OverloadedStrings #-}
module Muste.Sentence.Language
  (Language(Language), Grammar(Grammar))
  where

import Prelude ()
import Muste.Prelude
import Muste.Prelude.SQL (FromField, ToField)

import Data.Aeson (ToJSON(..), FromJSON(..), (.=), (.:))
import qualified Data.Aeson as Aeson
import GHC.Generics (Generic)
import Data.String

newtype Grammar = Grammar Text

deriving instance Show Grammar
deriving instance Eq Grammar
deriving instance Ord Grammar
deriving instance FromJSON Grammar
deriving instance ToJSON Grammar
deriving instance Generic Grammar
instance Binary Grammar where
deriving instance FromField Grammar
deriving instance ToField Grammar
deriving instance IsString Grammar

data Language = Language
  -- NB This field is not in use.
  { grammar  ∷ Grammar
  , lang     ∷ Text
  }

deriving instance Show Language
deriving instance Eq Language
deriving instance Ord Language

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
    $ \o → Language
    <$> o .: "grammar"
    <*> o .: "language"

deriving instance Generic Language
instance Binary Language where
