-- | Defines the shape of the requests/responses this API can handle.
--
-- Module      : Muste.Web.Ajax
-- License     : Artistic License 2.0
-- Stability   : experimental
-- Portability : POSIX
--
-- Many of the types are very similar to the ones defined in
-- "Muste.Web.Database.Types".  This is intentional. The reason for
-- this is that SQL database are row-orientend whereas JSON is
-- document oriented.

{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# language OverloadedStrings, DuplicateRecordFields , RecordWildCards,
  NamedFieldPuns #-}

module Muste.Web.Ajax
  ( ServerTree(..)
  , ClientTree(..)
  , LoginRequest(..)
  , ActiveLesson(..)
  , User(..)
  , CreateUser(..)
  , ChangePassword(..)
  , MenuRequest(..)
  , MenuList(..)
  , LoginToken(..)
  , LessonList(..)
  , MenuResponse(..)
  , MenuSettings(..)
  , HighScore(..)
  , Lesson(..)
  , Score(..)
  , Direction(..)
  , StartLesson(..)
  ) where

import Prelude ()
import Muste.Prelude

import Data.Aeson ((.:), (.=), (.:?), (.!=))
import Data.Aeson.Types (Parser)
import qualified Data.Aeson as Aeson

import Muste.Menu (Menu)
import Muste.Sentence.Unannotated (Unannotated)
import Muste.Sentence.Annotated (Annotated)

import qualified Muste.Web.Database.Types as Database

import           Muste.Web.Types.Score (Score(..))

data ClientTree = ClientTree
  { sentence      :: Unannotated
  -- Asking the client to supply these is a bit of a hack.  We just
  -- send it back unmodified!
  , direction     :: Direction
  }

deriving instance Show ClientTree

instance FromJSON ClientTree where
  parseJSON = Aeson.withObject "tree"
     $ \v -> ClientTree
    <$> v .: "sentence"
    <*> v .: "direction"

instance ToJSON ClientTree where
  toJSON ClientTree{..} = Aeson.object
    [ "sentence"  .= sentence
    , "direction" .= direction
    ]

data LoginRequest = LoginRequest
  { name     :: Text
  , password :: Text
  }
  

instance FromJSON LoginRequest where
  parseJSON = Aeson.withObject "login-request"
    $  \v -> LoginRequest
    <$> v .: "name"
    <*> v .: "password"

instance ToJSON LoginRequest where
  toJSON LoginRequest{..} = Aeson.object
    [ "name"     .= name
    , "password" .= password
    ]

data MenuRequest = MenuRequest
  { token    :: Database.Token
  , lesson   :: Lesson
  -- FIXME I feel like this should not be a part of the menu response.
  -- In stead we should store the score along with the users session,
  -- and only when the exercise is done respond with the final score.
  , score    :: Score
  , src      :: ClientTree
  , trg      :: ClientTree
  -- FIXME Ditto the comment about the field `score`.
  , settings :: Maybe MenuSettings
  }

instance ToJSON MenuRequest where
  toJSON MenuRequest{..} = Aeson.object
    [ "token"    .= token
    , "lesson"   .= lesson
    , "score"    .= score
    , "src"      .= src
    , "trg"      .= trg
    , "settings" .= settings
    ]

instance FromJSON MenuRequest where
  parseJSON = Aeson.withObject "menu-request"
    $  \b -> MenuRequest
    <$> b .:  "token"
    <*> b .:  "lesson"
    <*> b .:  "score"
    <*> b .:  "src"
    <*> b .:  "trg"
    <*> b .:? "settings"

data Direction = VersoRecto | RectoVerso

deriving stock instance Show Direction

instance FromJSON Direction where
  parseJSON val
    =   VersoRecto `aka` ["left-to-right", "ltr", "verso-recto"]
    <|> RectoVerso `aka` ["right-to-left", "rtl", "recto-verso"]
    where
    aka :: Direction
      -> [Text]
      -> Parser Direction
    aka d xs = oneOf $ step <$> xs
      where
      step kw = Aeson.withText "Direction" k val
        where
        k t = if kw == t then pure d else empty

instance ToJSON Direction where
  toJSON = \case
    VersoRecto -> "ltr"
    RectoVerso -> "rtl"

oneOf :: (Foldable t, Alternative f) => t (f a) -> f a
oneOf = foldl (<|>) empty

-- | 'ServerTree's represent the data needed to display a sentence in
-- the GUI.  The naming is maybe not the best, but the reason it is
-- called like that is simply because it is the data that the client
-- *receives* from the server (e.g. in the case of
-- @\/api\/lesson\/:lesson@ or @\/api\/menu@).  When the client
-- performs requests @ClientTree@ is used in stead.  I'm not entirely
-- sure if this impedence mismatch is strictly necessary, but one
-- reason for it of course is that less information is needed by the
-- server when receiving a request for e.g. @\/api\/menu@.
data ServerTree = ServerTree
  { sentence  :: Annotated
  , menu      :: Menu
  , direction :: Direction
  } deriving (Show)

instance FromJSON ServerTree where
  parseJSON = Aeson.withObject "server-tree" $ \v -> ServerTree
    <$> v .:  "sentence"
    <*> v .:  "menu"
    <*> v .:? "direction" .!= VersoRecto

instance ToJSON ServerTree where
  toJSON ServerTree{..} = Aeson.object
    [ "sentence"  .= sentence
    , "menu"      .= menu
    , "direction" .= direction
    ]


newtype LoginToken = LoginToken Database.Token

instance FromJSON LoginToken where
  parseJSON = Aeson.withObject "login-success"
    $ \ v ->  LoginToken
    <$> v .: "token"

instance ToJSON LoginToken where
  toJSON (LoginToken token) = Aeson.object
    [ "token" .= token
    ]

newtype LessonList = LessonList [ActiveLesson]

instance FromJSON LessonList where
  parseJSON = Aeson.withObject "lesson-list"
    $ \ v ->  LessonList
    <$> v .: "lessons"

instance ToJSON LessonList where
  toJSON (LessonList lessons) = Aeson.object
    [ "lessons" .= lessons
    ]

data MenuResponse = MenuResponse
  { lesson           :: Lesson
  -- This is the score for the exercise.  Not the lesson!  I think we
  -- should just remove this.
  , score            :: Score
  , menu             :: MenuList
  , lessonFinished   :: Bool
  , exerciseFinished :: Bool
  , settings         :: Maybe MenuSettings
  }

instance ToJSON MenuResponse where
  toJSON MenuResponse{..} =
    Aeson.object
      [ "lesson"        .= lesson
      , "score"         .= score
      , "menu"          .= menu
      , "lesson-over"   .= lessonFinished
      , "exercise-over" .= exerciseFinished
      , "settings"      .= settings
      ]

data MenuSettings = MenuSettings
  { highlightMatches :: Bool
  , showSourceSentence :: Bool
  }

deriving stock instance Show MenuSettings

instance ToJSON MenuSettings where
  toJSON MenuSettings{..} = Aeson.object
    [ "highlight-matches"    .= highlightMatches
    , "show-source-sentence" .= showSourceSentence
    ]

instance FromJSON MenuSettings where
  parseJSON = Aeson.withObject "settings"
     $ \v -> MenuSettings
    <$> v .: "highlight-matches"
    <*> v .: "show-source-sentence"

-- Better name might be menus?
data MenuList = MenuList
  { src     :: ServerTree
  , trg     :: ServerTree
  }

instance FromJSON MenuList where
  parseJSON = Aeson.withObject "menu"
    $ \ o -> MenuList
    <$> o .: "src"
    <*> o .: "trg"

instance ToJSON MenuList where
  toJSON MenuList{..} = Aeson.object
    [ "src"     .= src
    , "trg"     .= trg
    ]

data User = User
  { name     :: Text
  }

deriving stock instance Show User

instance FromJSON User where
  parseJSON = Aeson.withObject "user"
     $ \v -> User
    <$> v .: "name"

instance ToJSON User where
  toJSON User{..} = Aeson.object
    [ "name"       .= name
    ]

data CreateUser = CreateUser
  { name     :: Text
  , password :: Text
  }

deriving stock instance Show CreateUser

instance FromJSON CreateUser where
  parseJSON = Aeson.withObject "user"
     $ \v -> CreateUser
    <$> v .: "name"
    <*> v .: "password"

-- FIXME Should use ID in stead of name here!
-- | Like a 'CreateUser' but with an old and a new password.
data ChangePassword = ChangePassword
  { name        :: Text
  , oldPassword :: Text
  , newPassword :: Text
  }

deriving stock instance Show ChangePassword

instance FromJSON ChangePassword where
  parseJSON = Aeson.withObject "user"
     $ \v -> ChangePassword
    <$> v .: "name"
    <*> v .: "old-password"
    <*> v .: "new-password"

data Lesson = Lesson
  { key  :: Database.Key Database.Lesson
  , name :: Text
  }

deriving stock instance Show Lesson

instance ToJSON Lesson where
  toJSON Lesson{..} = Aeson.object
    [ "key"        .= key
    , "name"       .= name
    ]

instance FromJSON Lesson where
  parseJSON = Aeson.withObject "user"
     $ \v -> Lesson
    <$> v .: "key"
    <*> v .: "name"

data HighScore = HighScore
  { lesson     :: Lesson
  , user       :: User
  , score      :: Score
  }

deriving stock instance Show HighScore

instance ToJSON HighScore where
  toJSON HighScore{..} = Aeson.object
    [ "lesson"     .= lesson
    , "user"       .= user
    , "score"      .= score
    ]

data ActiveLesson = ActiveLesson
  { lesson        :: Database.Key Database.Lesson
  , name          :: Text
  , exercisecount :: Database.Numeric
  , passedcount   :: Database.Numeric
  , score         :: Maybe Score
  , finished      :: Bool
  , enabled       :: Bool
  }

deriving stock    instance Show    ActiveLesson
deriving stock    instance Generic ActiveLesson

instance FromJSON ActiveLesson where
  parseJSON = Aeson.withObject "Lesson"
    $ \v -> ActiveLesson
    <$> v .: "lesson"
    <*> v .: "name"
    <*> v .: "exercisecount"
    <*> v .: "passedcount"
    <*> v .: "score"
    <*> v .: "passed"
    <*> v .: "enabled"

instance ToJSON ActiveLesson where
  toJSON ActiveLesson{..} = Aeson.object
    [ "lesson"        .= lesson
    , "name"          .= name
    , "exercisecount" .= exercisecount
    , "passedcount"   .= passedcount
    , "score"         .= score
    , "passed"        .= finished
    , "enabled"       .= enabled
    ]


data StartLesson = StartLesson
  { token   :: Database.Token
  , lesson  :: Database.Key Database.Lesson
  , restart :: Bool
  }

deriving stock    instance Show    StartLesson
deriving stock    instance Generic StartLesson

instance FromJSON StartLesson where
  parseJSON = Aeson.withObject "StartLesson"
    $ \v -> StartLesson
    <$> v .:  "token"
    <*> v .:  "lesson"
    <*> v .:? "restart" .!= False

instance ToJSON StartLesson where
  toJSON StartLesson{..} = Aeson.object
    [ "token"   .= token
    , "lesson"  .= lesson
    , "restart" .= restart
    ]

