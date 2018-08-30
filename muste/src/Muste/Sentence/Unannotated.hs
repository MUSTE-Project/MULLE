{-# OPTIONS_GHC -Wall -Wno-type-defaults #-}
{-# Language NamedFieldPuns, RecordWildCards, OverloadedStrings #-}
module Muste.Sentence.Unannotated where

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
import Muste.Sentence.Annotated (Annotated)
import qualified Muste.Sentence.Annotated as Annotated

data Unannotated = Unannotated
  { language      ∷ Language
  , linearization ∷ Linearization Token.Unannotated
  }

deriving instance Show Unannotated
deriving instance Eq Unannotated
deriving instance Ord Unannotated

instance ToJSON Unannotated where
  toJSON (Unannotated {..}) = Aeson.object
    [ "language"      .= language
    , "linearization" .= linearization
    ]

instance FromJSON Unannotated where
  parseJSON = Aeson.withObject "word"
    $ \o → Unannotated
    <$> o .: "language"
    <*> o .: "linearization"

deriving instance Generic Unannotated
instance Binary Unannotated where

instance ToField Unannotated where
  toField = SQL.toBlob

instance FromField Unannotated where
  fromField = SQL.fromBlob

instance Sentence Unannotated where
  language = Muste.Sentence.Unannotated.language
  type Token Unannotated = Token.Unannotated
  linearization = Muste.Sentence.Unannotated.linearization
  sentence = Unannotated

unambiguous
  ∷ MonadThrow m
  ⇒ Exception e
  ⇒ e
  → Context
  → Unannotated
  → m Annotated
unambiguous e c@(Context { .. }) s
  = linearization s
  & Sentence.stringRep
  & Grammar.parseSentence ctxtGrammar ctxtLang
  & map unambigSimpl
  & Annotated.merge e
  where
  unambigSimpl ∷ TTree → Annotated
  unambigSimpl t
    = Annotated.annotated c l t t t
  l ∷ Language
  l = Sentence.language s
