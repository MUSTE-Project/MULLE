{-# OPTIONS_GHC -Wall -Wno-type-defaults #-}
{-# Language NamedFieldPuns, RecordWildCards, OverloadedStrings #-}
module Muste.Sentence.Unannotated where

import Prelude ()
import Muste.Prelude
import Data.Aeson (ToJSON(..), FromJSON(..), (.=), (.:))
import qualified Data.Aeson as Aeson
import GHC.Generics (Generic)
import Data.Function ((&))
import GHC.Exts (fromList)
import Data.MonoTraversable
import qualified Data.Text as Text

import Muste.Tree.Internal (TTree)
import Muste.Linearization.Internal (Context(..))
import qualified Muste.Grammar.Internal as Grammar
import Muste.Common.SQL (FromField, ToField)
import qualified Muste.Common.SQL as SQL
import qualified Muste.Sentence.Token as Token
import Muste.Sentence.Class
  ( Sentence
  , Language(Language)
  , Linearization
  , Grammar(Grammar)
  )
import qualified Muste.Sentence.Linearization as Linearization
import qualified Muste.Sentence.Class as Sentence
import qualified Muste.Linearization.Internal as OldLinearization
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
  toJSON Unannotated{..} = Aeson.object
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

annotate
  ∷ MonadThrow m
  ⇒ Exception e
  ⇒ e
  → Context
  → Unannotated
  → m Annotated
annotate e c@Context{..} s
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

-- | @'mkLinearization' c src trg t@ creates a 'Linearization' of @t@
-- from a source tree (@src@) and a target tree (@trg@).  The
-- 'Linearization' will be a valid such in the grammar and languages
-- specified by the 'Context' @c@.
--
-- This implementation reuses the functionality from
-- 'Muste.Linearization.Internal.mkLin' and then converts it to the
-- new representation.  In doing so note in particular that we do not
-- create ambiguities in the individual words.  Eachs 'Token' will
-- correspond exactly to an internal node in the 'TTree' (idenfitied
-- by the "name" of that node).
mkLinearization
  ∷ Context
  → TTree
  → TTree
  → TTree -- ^ The actual tree to linearize
  → Linearization Token.Unannotated
mkLinearization c t0 t1 t
  -- Reuse functionality from 'Muste.Linearization.Internal'
  = OldLinearization.mkLin c t0 t1 t
  & otoList
  -- Convert old representation to new.
  & fmap step
  & fromList
  where
  step ∷ OldLinearization.LinToken → Token.Unannotated
  step (OldLinearization.LinToken { .. })
    = Token.unannotated ltlin

-- | @'sentence' c src trg t@ creates a 'Sentence' of @t@ from a
-- source tree (@src@) and a target tree (@trg@).  The 'Sentence' will
-- be a valid such in the grammar and languages specified by the
-- 'Context' @c@.
--
-- See also the documentation for 'linearization'.
unannotated
  ∷ Context
  → Language
  → TTree -- ^ The source tree
  → TTree -- ^ The target tree
  → TTree -- ^ The actual tree to linearize
  → Unannotated
unannotated c l src trg t
  = Unannotated l $ mkLinearization c src trg t

stringRep ∷ Unannotated → Text
stringRep = linearization >>> Linearization.stringRep

fromText
  ∷ Text -- ^ An identifier for the grammar
  → Text -- ^ The language
  → Text -- ^ The sentence
  → Unannotated
fromText g l xs
  = Unannotated (Language (Grammar g) l) (fromList (go <$> Text.words xs))
  where
  go ∷ Text → Token.Unannotated
  go = Token.Unannotated
