{-# OPTIONS_GHC -Wall -Wno-type-defaults #-}
{-# Language NamedFieldPuns, RecordWildCards, OverloadedStrings #-}
module Muste.Sentence.Annotated
  (Annotated, annotated, merge)
  where

import Data.Maybe
import Prelude hiding (Word)
import Data.Aeson (ToJSON(..), FromJSON(..), (.=), (.:))
import qualified Data.Aeson as Aeson
import GHC.Generics (Generic)
import Data.Binary hiding (Word)
import Data.Function ((&))
import Data.MonoTraversable
import GHC.Exts (fromList)
import Control.Category ((>>>))
import qualified Data.Vector as Vector
import Data.Function (on)
import Control.Monad.Catch (MonadThrow(throwM), Exception)

import Muste.Sentence.Token (IsToken)
import qualified Muste.Sentence.Token as Token
import Muste.Sentence.Class (Sentence, Language, Linearization, Token)
import qualified Muste.Sentence.Class as Sentence

import Muste.Common.SQL (FromField, ToField)
import qualified Muste.Common.SQL as SQL

import Muste.Tree.Internal (TTree)
import qualified Muste.Tree.Internal as Tree
import Muste.Linearization.Internal (Context)
import qualified Muste.Linearization.Internal as OldLinearization

data Annotated = Annotated
  { language      ∷ Language
  , linearization ∷ Linearization Token.Annotated
  }

deriving instance Show Annotated

instance ToJSON Annotated where
  toJSON (Annotated {..}) = Aeson.object
    [ "language"      .= language
    , "linearization" .= linearization
    ]

instance FromJSON Annotated where
  parseJSON = Aeson.withObject "word"
    $ \o → Annotated
    <$> o .: "language"
    <*> o .: "linearization"

deriving instance Generic Annotated
instance Binary Annotated where

instance ToField Annotated where
  toField = SQL.toBlob

instance FromField Annotated where
  fromField = SQL.fromBlob

instance Sentence Annotated where
  -- This is not a loop.  The 'sentence' on the RHS is defined in this
  -- module.  The other one is a class method (which happen to be
  -- imported qualified as 'Sentence.language')
  language = Muste.Sentence.Annotated.language
  type Token Annotated = Token.Annotated
  linearization = Muste.Sentence.Annotated.linearization
  sentence = Annotated

-- | @'mkLinearization' c src trg t@ creates a 'Linearization' of @t@
-- from a source tree (@src@) and a target tree (@trg@).  The
-- 'Linearization' will be a valid such in the grammar and languages
-- specified by the 'Context' @c@.
--
-- This implementation reuses the functionality from
-- 'Muste.OldLinearization.Internal.mkLin' and then converts it to the
-- new representation.  In doing so note in particular that we do not
-- create ambiguities in the individual words.  Eachs 'Token' will
-- correspond exactly to an internal node in the 'TTree' (idenfitied
-- by the "name" of that node).
mkLinearization
  ∷ Context
  → TTree
  → TTree
  → TTree -- ^ The actual tree to linearize
  → Linearization Token.Annotated
mkLinearization c t0 t1 t
  -- Reuse functionality from 'Muste.OldLinearization.Internal'
  = OldLinearization.mkLin c t0 t1 t
  & otoList
  -- Convert old representation to new.
  & fmap step
  & fromList
  where
  step ∷ OldLinearization.LinToken → Token.Annotated
  step (OldLinearization.LinToken { .. })
    = Token.annotated ltlin (fromList @[String] $ names ltpath)
  -- Throws if the path is not found /and/ only finds a single
  -- function name!
  names ∷ Tree.Path → [String]
  names
    =   Tree.selectNode @TTree t
    >>> fromMaybe (error "Expected to find path here")
    >>> name
    >>> pure @[]
  name ∷ TTree → String
  name = \case
    Tree.TNode n _ _ → n
    Tree.TMeta{} → error "Expected saturated tree"

-- | @'sentence' c src trg t@ creates a 'Sentence' of @t@ from a
-- source tree (@src@) and a target tree (@trg@).  The 'Sentence' will
-- be a valid such in the grammar and languages specified by the
-- 'Context' @c@.
--
-- See also the documentation for 'linearization'.
annotated
  ∷ Context
  → Language
  → TTree -- ^ The source tree
  → TTree -- ^ The target tree
  → TTree -- ^ The actual tree to linearize
  → Annotated
annotated c l src trg t
  = Annotated l $ mkLinearization c src trg t


-- | Merge multiple
merge ∷ MonadThrow m ⇒ Exception e ⇒ e → [Annotated] → m Annotated
merge e = \case
  [] → throwM e
  xs → pure $ foldl1 merge1 xs

-- Merge two sentences, assuming they have the same language.
merge1 ∷ Annotated → Annotated → Annotated
merge1 a b = Annotated lang ((mergeL `on` linearization) a b)
  where
  lang = language a

mergeL
  ∷ IsToken Token.Annotated
  ⇒ Linearization Token.Annotated
  → Linearization Token.Annotated
  → Linearization Token.Annotated
mergeL (Sentence.Linearization a) (Sentence.Linearization b)
  = Sentence.Linearization (Vector.zipWith Token.mergeAnnotated a b)
