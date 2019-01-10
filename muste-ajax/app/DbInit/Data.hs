-- | Data used for inititializing the database

{-# Language OverloadedStrings, OverloadedLists, DuplicateRecordFields #-}
{-# OPTIONS_GHC -Wall #-}

module DbInit.Data
  ( SearchOptions(..)
  , LessonSettings(..)
  , Sentence(..)
  , Languages(..)
  , Exercise(..)
  , Lesson(..)
  , Ajax.Direction(..)
  ) where

import Prelude ()
import Muste.Prelude

import Data.Text (Text)
import Data.Aeson ((.:), FromJSON, Object, (.:?), (.!=))
import Data.Aeson.Types (Parser)
import qualified Data.Aeson as Aeson

import qualified Muste.Web.Database.Types as Database
import qualified Muste.Web.Ajax as Ajax

-- | A combinator that defaults to 'mempty' is not value is present.
(.:*) ∷ FromJSON a ⇒ Monoid a ⇒ Object → Text → Parser a
o .:* a = o .:? a .!= mempty

data SearchOptions = SearchOptions
  { searchDepthLimit ∷ Maybe Int
  , searchSizeLimit  ∷ Maybe Int
  }

deriving stock instance Show SearchOptions

instance Semigroup SearchOptions where
  SearchOptions a0 b0 <> SearchOptions a1 b1
    = SearchOptions (s a0 a1) (s b0 b1)
    where
    s a b = (+) <$> a <*> b

instance Monoid SearchOptions where
  mempty = SearchOptions Nothing Nothing

instance FromJSON SearchOptions where
  parseJSON = Aeson.withObject "search-options"
    $  \v → SearchOptions
    <$> v .:? "depth"
    <*> v .:? "size"

data LessonSettings = LessonSettings
  { grammar          ∷ Text
  , enabled          ∷ Bool
  , repeatable       ∷ Bool
  , srcDir           ∷ Ajax.Direction
  , trgDir           ∷ Ajax.Direction
  , highlightMatches ∷ Bool
  , showSourceSentence ∷ Bool
  -- How many exercises need to be solved for the lesson to be
  -- considered solved.
  , exerciseCount    ∷ Maybe Int
  -- Randomize the order of the exercises.
  , randomizeOrder   ∷ Bool
  }

deriving stock instance Show LessonSettings

instance FromJSON LessonSettings where
  parseJSON = Aeson.withObject "search-options"
    $  \v → LessonSettings
    <$> v .:  "grammar"
    <*> v .:? "enabled"                  .!= True
    <*> v .:? "repeatable"               .!= True
    <*> v .:? "source-direction"         .!= Ajax.VersoRecto
    <*> v .:? "target-direction"         .!= Ajax.VersoRecto
    <*> v .:? "highlight-matches"        .!= True
    <*> v .:? "show-source-sentence"     .!= True
    <*> v .:? "exercise-count"
    <*> v .:? "randomize-exercise-order" .!= False

newtype Sentence = Sentence Text

deriving stock instance Show Sentence

deriving newtype instance FromJSON Sentence

data Languages = Languages
  { source ∷ Text
  , target ∷ Text
  }

deriving stock instance Show Languages

instance FromJSON Languages where
  parseJSON = Aeson.withObject "exercise"
    $  \v → Languages
    <$> v .:  "source"
    <*> v .:  "target"

data Exercise = Exercise
  { source ∷ Sentence
  , target ∷ Sentence
  }

deriving stock instance Show Exercise

instance FromJSON Exercise where
  parseJSON = Aeson.withObject "exercise"
    $  \v → Exercise
    <$> v .:  "source"
    <*> v .:  "target"

data Lesson = Lesson
  { key            ∷ Database.Key Database.Lesson
  , name           ∷ Text
  , description    ∷ Text
  , settings       ∷ LessonSettings
  , searchOptions  ∷ SearchOptions
  , languages      ∷ Languages
  , exercises'     ∷ [Exercise]
  }

deriving stock instance Show Lesson

instance FromJSON Lesson where
  parseJSON = Aeson.withObject "search-options"
    $  \v → Lesson
    <$> v .:  "key"
    <*> v .:  "name"
    <*> v .:  "description"
    <*> v .:  "settings"
    <*> v .:* "search-options"
    <*> v .:  "languages"
    <*> v .:  "exercises"

