{-# OPTIONS_GHC -Wall #-}
{-# Language
 DeriveGeneric,
 FlexibleContexts,
 NamedFieldPuns,
 OverloadedStrings,
 RecordWildCards,
 StandaloneDeriving,
 TypeApplications,
 TypeFamilies
#-}

module Muste.Sentence.Annotated
  (Annotated, annotated, merge, mergeL, mkLinearization)
  where


import Muste.Util (toBlob, fromBlob)
import Database.SQLite.Simple.ToField (ToField(..))
import Database.SQLite.Simple.FromField (FromField(..))

import Control.Monad.Catch (MonadThrow(throwM), Exception)
import Control.Category ((>>>))
import Data.Function ((&), on)
import GHC.Generics (Generic)

import Data.Aeson (ToJSON(..), FromJSON(..), (.=), (.:))
import qualified Data.Aeson as Aeson
import Data.Binary (Binary)
import Data.MonoTraversable (otoList)
import Data.Text (Text)
import Data.Maybe (fromMaybe)
import qualified Data.Vector as Vector
import GHC.Exts (fromList)

import Muste.Sentence.Token (IsToken)
import qualified Muste.Sentence.Token as Token
import Muste.Sentence.Class (Sentence, Language, Linearization, Token)
import qualified Muste.Sentence.Class as Sentence

import Muste.Tree.Internal (TTree, Category)
import qualified Muste.Tree.Internal as Tree
import Muste.Linearization.Internal (Context)
import qualified Muste.Linearization.Internal as OldLinearization


data Annotated = Annotated
  { language      :: Language
  , linearization :: Linearization Token.Annotated
  }

deriving instance Show Annotated

instance ToJSON Annotated where
  toJSON (Annotated {..}) = Aeson.object
    [ "language"      .= language
    , "linearization" .= linearization
    ]

instance FromJSON Annotated where
  parseJSON = Aeson.withObject "word"
    $ \o -> Annotated
    <$> o .: "language"
    <*> o .: "linearization"

deriving instance Generic Annotated
instance Binary Annotated where

instance ToField Annotated where
  toField = toBlob

instance FromField Annotated where
  fromField = fromBlob

instance Sentence Annotated where
  -- This is not a loop.  The 'sentence' on the RHS is defined in this
  -- module.  The other one is a class method (which happen to be
  -- imported qualified as 'Sentence.language')
  language = Muste.Sentence.Annotated.language
  type Token Annotated = Token.Annotated
  linearization = Muste.Sentence.Annotated.linearization
  sentence = Annotated

-- | @'mkLinearization' c t@ creates a 'Linearization' of @t@. The
-- 'Linearization' will be a valid such in the grammar and languages
-- specified by the 'Context' @c@.
--
-- This implementation reuses the functionality from
-- 'Muste.OldLinearization.Internal.mkLin' and then converts it to the
-- new representation.  In doing so note in particular that we do not
-- create ambiguities in the individual words.  Eachs 'Token' will
-- correspond exactly to an internal node in the 'TTree' (idenfitied
-- by the "name" of that node).
mkLinearization :: Context -> TTree -> Linearization Token.Annotated
mkLinearization c t
  -- Reuse functionality from 'Muste.OldLinearization.Internal'
  = OldLinearization.linearizeTree c t
  & otoList
  -- Convert old representation to new.
  & fmap step
  & fromList
  where
  step :: OldLinearization.LinToken -> Token.Annotated
  step (OldLinearization.LinToken { .. })
    = Token.annotated ltlin (fromList @[Text] $ names ltpath)
  -- Throws if the path is not found /and/ only finds a single
  -- function name!
  names :: Tree.Path -> [Text]
  names
    =   Tree.selectNode t
    >>> fromMaybe (error "Expected to find path here")
    >>> name
    >>> Tree.unCategory
    >>> pure @[]
  name :: TTree -> Category
  name (Tree.TNode n _ _) = n
  name (Tree.TMeta _)     = error "Expected saturated tree"

-- | @'annotated' c t@ creates a 'Sentence' of @t@.  The 'Sentence' 
-- will be a valid such in the grammar and languages specified by the
-- 'Context' @c@.
--
-- See also the documentation for 'linearization'.
annotated :: Context -> Language -> TTree -> Annotated
annotated c l t = Annotated l $ mkLinearization c t

-- | Merge multiple
merge :: MonadThrow m => Exception e => e -> [Annotated] -> m Annotated
merge e [] = throwM e
merge _ xs = pure $ foldl1 merge1 xs

-- Merge two sentences, assuming they have the same language.
merge1 :: Annotated -> Annotated -> Annotated
merge1 a b = Annotated lang ((mergeL `on` linearization) a b)
  where
  lang = language a

mergeL
  :: IsToken Token.Annotated
  => Linearization Token.Annotated
  -> Linearization Token.Annotated
  -> Linearization Token.Annotated
mergeL (Sentence.Linearization a) (Sentence.Linearization b)
  = Sentence.Linearization (Vector.zipWith Token.mergeAnnotated a b)
