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
  , Database.ActiveLesson(..)
  , User(..)
  , CreateUser(..)
  , ChangePassword(..)
  , MenuRequest(..)
  , MenuList(..)
  , LoginSuccess(..)
  , LessonList(..)
  , MenuResponse(..)
  , HighScore(..)
  , Lesson(..)
  , Score(..)
  ) where

import Prelude ()
import Muste.Prelude

import Data.Aeson ((.:), (.=), (.:?))
import qualified Data.Aeson as Aeson

import Muste
import Muste.Sentence.Unannotated (Unannotated)
import Muste.Sentence.Annotated (Annotated)

import qualified Muste.Web.Database.Types as Database

import           Muste.Web.Types.Score (Score(..))

newtype ClientTree = ClientTree { unClientTree ∷ Unannotated }

deriving instance Show ClientTree

instance FromJSON ClientTree where
  parseJSON = Aeson.withObject "tree"
     $ \v -> ClientTree
    <$> v .: "sentence"

instance ToJSON ClientTree where
  toJSON (ClientTree sentence) = Aeson.object
    [ "sentence" .= sentence
    ]

data LoginRequest = LoginRequest
  { name     ∷ Text
  , password ∷ Text
  }
  

instance FromJSON LoginRequest where
  parseJSON = Aeson.withObject "login-request"
    $  \v → LoginRequest
    <$> v .: "name"
    <*> v .: "password"

instance ToJSON LoginRequest where
  toJSON LoginRequest{..} = Aeson.object
    [ "name"     .= name
    , "password" .= password
    ]

data MenuRequest = MenuRequest
  { lesson ∷ Lesson
  -- FIXME I feel like this should not be a part of the menu response.
  -- In stead we should store the score along with the users session,
  -- and only when the exercise is done respond with the final score.
  , score  ∷ Score
  , src    ∷ ClientTree
  , trg    ∷ ClientTree
  }

instance ToJSON MenuRequest where
  toJSON MenuRequest{..} = Aeson.object
    [ "lesson" .= lesson
    , "score"  .= score
    , "src"    .= src
    , "trg"    .= trg
    ]

instance FromJSON MenuRequest where
  parseJSON = Aeson.withObject "menu-request"
    $  \b → MenuRequest
    <$> b .: "lesson"
    <*> b .: "score"
    <*> b .: "src"
    <*> b .: "trg"

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
  { sentence  ∷ Annotated
  , menu      ∷ Menu
  } deriving (Show)

instance FromJSON ServerTree where
  parseJSON = Aeson.withObject "server-tree" $ \v -> ServerTree
    <$> v .: "sentence"
    <*> v .: "menu"

instance ToJSON ServerTree where
  toJSON ServerTree{..} = Aeson.object
    [ "sentence" .= sentence
    , "menu"     .= menu
    ]

data LoginSuccess = LoginSuccess Text

instance FromJSON LoginSuccess where
  parseJSON = Aeson.withObject "login-success"
    $ \ v →  LoginSuccess
    <$> v .: "token"

instance ToJSON LoginSuccess where
  toJSON (LoginSuccess token) = Aeson.object
    [ "login-succes" .= token
    ]

data LessonList = LessonList [Database.ActiveLesson]

instance FromJSON LessonList where
  parseJSON = Aeson.withObject "lesson-list"
    $ \ v →  LessonList
    <$> v .: "lessons"

instance ToJSON LessonList where
  toJSON (LessonList lessons) = Aeson.object
    [ "lessons" .= lessons
    ]

data MenuResponse = MenuResponse
  -- A key to the lesson
  { lesson     ∷ Lesson
  -- This is the score for the exercise.  Not the lesson!  I think we
  -- should just remove this.
  , score      ∷ Score
  , menu       ∷ Maybe MenuList
  , finished   ∷ Bool
  }

instance FromJSON MenuResponse where
  parseJSON = Aeson.withObject "menu"
    $ \ o → MenuResponse
    <$> o .:  "lesson"
    <*> o .:  "score"
    <*> o .:? "menu"
    <*> o .:  "lesson-over"

instance ToJSON MenuResponse where
  toJSON MenuResponse{..} =
    Aeson.object
      [ "lesson"      .= lesson
      , "score"       .= score
      , "menu"        .= menu
      , "lesson-over" .= finished
      ]

-- Better name might be menus?
data MenuList = MenuList
  { src     ∷ ServerTree
  , trg     ∷ ServerTree
  }

instance FromJSON MenuList where
  parseJSON = Aeson.withObject "menu"
    $ \ o → MenuList
    <$> o .: "src"
    <*> o .: "trg"

instance ToJSON MenuList where
  toJSON MenuList{..} = Aeson.object
    [ "src"     .= src
    , "trg"     .= trg
    ]

data User = User
  { key      ∷ Database.Key
  , name     ∷ Text
  }

deriving stock instance Show User

instance FromJSON User where
  parseJSON = Aeson.withObject "user"
     $ \v -> User
    <$> v .: "key"
    <*> v .: "name"

instance ToJSON User where
  toJSON User{..} = Aeson.object
    [ "key"        .= key
    , "name"       .= name
    ]

data CreateUser = CreateUser
  { name     ∷ Text
  , password ∷ Text
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
  { name        ∷ Text
  , oldPassword ∷ Text
  , newPassword ∷ Text
  }

deriving stock instance Show ChangePassword

instance FromJSON ChangePassword where
  parseJSON = Aeson.withObject "user"
     $ \v -> ChangePassword
    <$> v .: "name"
    <*> v .: "old-password"
    <*> v .: "new-password"

data Lesson = Lesson
  { key  ∷ Database.Key
  , name ∷ Text
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
  { lesson     ∷ Lesson
  , user       ∷ User
  , score      ∷ Score
  }

deriving stock instance Show HighScore

instance ToJSON HighScore where
  toJSON HighScore{..} = Aeson.object
    [ "lesson"     .= lesson
    , "user"       .= user
    , "score"      .= score
    ]
