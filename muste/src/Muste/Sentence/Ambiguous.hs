{-# OPTIONS_GHC -Wall -Wno-type-defaults #-}
{-# Language NamedFieldPuns, RecordWildCards, OverloadedStrings #-}
module Muste.Sentence.Ambiguous where

import Prelude hiding (Word)
import Data.Aeson (ToJSON(..), FromJSON(..), (.=), (.:))
import qualified Data.Aeson as Aeson
import GHC.Generics (Generic)
import Data.Binary hiding (Word)
import Data.Function ((&))
import Control.Monad.Catch (MonadThrow, Exception)

import Muste.Tree.Internal (TTree)
import Muste.Linearization.Internal (Context(..))
import Muste.Grammar.Internal as Grammar
import Muste.Common.SQL (FromField, ToField)
import qualified Muste.Common.SQL as SQL
import qualified Muste.Sentence.Token as Token
import Muste.Sentence.Class (Sentence, Language, Linearization)
import qualified Muste.Sentence.Class as Sentence
import Muste.Sentence.Unambiguous (Unambiguous)
import qualified Muste.Sentence.Unambiguous as Unambiguous

data Ambiguous = Ambiguous
  { language      ∷ Language
  , linearization ∷ Linearization Token.Ambiguous
  }

deriving instance Show Ambiguous
deriving instance Eq Ambiguous
deriving instance Ord Ambiguous

instance ToJSON Ambiguous where
  toJSON (Ambiguous {..}) = Aeson.object
    [ "language"      .= language
    , "linearization" .= linearization
    ]

instance FromJSON Ambiguous where
  parseJSON = Aeson.withObject "word"
    $ \o → Ambiguous
    <$> o .: "language"
    <*> o .: "linearization"

deriving instance Generic Ambiguous
instance Binary Ambiguous where

instance ToField Ambiguous where
  toField = SQL.toBlob

instance FromField Ambiguous where
  fromField = SQL.fromBlob

instance Sentence Ambiguous where
  language = Muste.Sentence.Ambiguous.language
  type Token Ambiguous = Token.Ambiguous
  linearization = Muste.Sentence.Ambiguous.linearization
  sentence = Ambiguous

unambiguous
  ∷ MonadThrow m
  ⇒ Exception e
  ⇒ e
  → Context
  → Ambiguous
  → m Unambiguous
unambiguous e c@(Context { .. }) s
  = linearization s
  & Sentence.stringRep
  & Grammar.parseSentence ctxtGrammar ctxtLang
  & map unambigSimpl
  & Unambiguous.merge e
  where
  unambigSimpl ∷ TTree → Unambiguous
  unambigSimpl t
    = Unambiguous.unambiguous c l t t t
  l ∷ Language
  l = Sentence.language s
