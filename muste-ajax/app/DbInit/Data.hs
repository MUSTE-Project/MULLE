-- | Data used for inititializing the database

{-# Language OverloadedStrings, OverloadedLists, DuplicateRecordFields, RecordWildCards #-}
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
import Data.Aeson (Object, FromJSON(..), ToJSON(..), (.:), (.:?), (.!=), (.=))
import Data.Aeson.Types (Parser)
import qualified Data.Aeson as Aeson

import qualified Muste.Web.Database.Types as Database
import qualified Muste.Web.Ajax as Ajax


-- | A combinator that defaults to an empty object if no value is present.
(.:*) :: FromJSON a => Object -> Text -> Parser a
o .:* a = o .:? a .!= emptyObject
  where emptyObject
          = case Aeson.decode "{}" of
              Just obj -> obj
              Nothing  -> error "emptyObjectParser: error parsing empty object"


-- Search options

data SearchOptions = SearchOptions
  { searchDepthLimit :: Maybe Int
  , searchSizeLimit  :: Maybe Int
  }

deriving stock instance Show SearchOptions

instance FromJSON SearchOptions where
  parseJSON = Aeson.withObject "search-options"
    $  \v -> SearchOptions
    <$> v .:? "depth"
    <*> v .:? "size"

instance ToJSON SearchOptions where
  toJSON SearchOptions{..} = Aeson.object
    [ "depth" .= searchDepthLimit
    , "size"  .= searchSizeLimit
    ]


-- Lesson settings

data LessonSettings = LessonSettings
  { enabled          :: Bool
  , repeatable       :: Bool
  , srcDir           :: Ajax.Direction
  , trgDir           :: Ajax.Direction
  , highlightMatches :: Bool
  , showSourceSentence :: Bool
  -- How many exercises need to be solved for the lesson to be
  -- considered solved.
  , exerciseCount    :: Maybe Int
  -- Randomize the order of the exercises.
  , randomizeOrder   :: Bool
  }

deriving stock instance Show LessonSettings

instance FromJSON LessonSettings where
  parseJSON = Aeson.withObject "search-options"
    $  \v -> LessonSettings
    <$> v .:? "enabled"                  .!= True
    <*> v .:? "repeatable"               .!= True
    <*> v .:? "source-direction"         .!= Ajax.VersoRecto
    <*> v .:? "target-direction"         .!= Ajax.VersoRecto
    <*> v .:? "highlight-matches"        .!= True
    <*> v .:? "show-source-sentence"     .!= True
    <*> v .:? "exercise-count"
    <*> v .:? "randomize-exercise-order" .!= False

instance ToJSON LessonSettings where
  toJSON LessonSettings{..} = Aeson.object
    [ "enabled"                  .= enabled
    , "repeatable"               .= repeatable
    , "source-direction"         .= srcDir
    , "target-direction"         .= trgDir
    , "highlight-matches"        .= highlightMatches
    , "show-source-sentence"     .= showSourceSentence
    , "exercise-count"           .= exerciseCount
    , "randomize-exercise-order" .= randomizeOrder
    ]


-- Sentences (strings)

newtype Sentence = Sentence Text

deriving stock instance Show Sentence

deriving newtype instance FromJSON Sentence

deriving newtype instance ToJSON Sentence


-- Languages (source, target)

data Languages = Languages
  { source :: Text
  , target :: Text
  }

deriving stock instance Show Languages

instance FromJSON Languages where
  parseJSON = Aeson.withObject "exercise"
    $  \v -> Languages
    <$> v .:  "source"
    <*> v .:  "target"

instance ToJSON Languages where
  toJSON Languages{..} = Aeson.object
    [ "source" .= source
    , "target" .= target
    ]


-- Exercises (source, target sentence)

data Exercise = Exercise
  { source :: Sentence
  , target :: Sentence
  }

deriving stock instance Show Exercise

instance FromJSON Exercise where
  parseJSON = Aeson.withObject "exercise"
    $  \v -> Exercise
    <$> v .:  "source"
    <*> v .:  "target"

instance ToJSON Exercise where
  toJSON Exercise{..} = Aeson.object
    [ "source" .= source
    , "target" .= target
    ]


-- Lessons

data Lesson = Lesson
  { key            :: Database.Key Database.Lesson
  , name           :: Text
  , description    :: Text
  , settings       :: LessonSettings
  , searchOptions  :: SearchOptions
  , grammar        :: Text
  , languages      :: Languages
  , exercises'     :: [Exercise]
  }

deriving stock instance Show Lesson

instance FromJSON Lesson where
  parseJSON = Aeson.withObject "lesson"
    $  \v -> Lesson
    <$> v .:  "key"
    <*> v .:  "name"
    <*> v .:  "description"
    <*> v .:* "settings"
    <*> v .:* "search-options"
    <*> v .:  "grammar"
    <*> v .:  "languages"
    <*> v .:  "exercises"

instance ToJSON Lesson where
  toJSON Lesson{..} = Aeson.object
    [ "key"            .= key
    , "name"           .= name
    , "description"    .= description
    , "settings"       .= settings
    , "search-options" .= searchOptions
    , "grammar"        .= grammar
    , "languages"      .= languages
    , "exercises"      .= exercises'
    ]
