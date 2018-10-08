{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# language OverloadedStrings, DuplicateRecordFields , RecordWildCards,
  NamedFieldPuns #-}
module Ajax
  ( ServerTree
  , ClientTree(ClientTree)
  , LessonInit(..)
  , LoginRequest(..)
  , Lesson2(..)
  , User(..)
  , ChangePwd(..)
  , MenuRequest(..)
  , MenuList(..)
  , LoginSuccess(..)
  , LessonList(..)
  , serverTree
  , unClientTree
  ) where

import Prelude ()
import Muste.Prelude

import Data.Aeson ((.:), (.=))
import qualified Data.Aeson as Aeson
import Data.Text (Text)
import Data.Time

import Muste
import Muste.Sentence.Unannotated (Unannotated)
import Muste.Sentence.Annotated (Annotated)

import Database (Lesson2(..))
import Types

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
  { username :: Text
  , password :: Text
  }
  
data LessonInit = LessonInit
  { lesson :: Text
  }

instance FromJSON LoginRequest where
  parseJSON = Aeson.withObject "login-request"
    $  \v → LoginRequest
    <$> v .: "username"
    <*> v .: "password"

instance ToJSON LoginRequest where
  toJSON LoginRequest{..} = Aeson.object
    [ "username" .= username
    , "password" .= password
    ]

instance FromJSON LessonInit where
  parseJSON = Aeson.withObject "lesson-init"
    $  \v → LessonInit
    <$> v .: "lesson"

instance ToJSON LessonInit where
  toJSON (LessonInit lesson) = Aeson.object
    [ "lesson" .= lesson
    ]

data MenuRequest = MenuRequest
  { lesson ∷ Text
  , score  ∷ Score
  , time   ∷ NominalDiffTime
  , src    ∷ ClientTree
  , trg    ∷ ClientTree
  }

instance ToJSON MenuRequest where
  toJSON MenuRequest{..} = Aeson.object
    [ "lesson" .= lesson
    , "score"  .= score
    , "time"   .= time
    , "src"    .= src
    , "trg"    .= trg
    ]

instance FromJSON MenuRequest where
  parseJSON = Aeson.withObject "menu-request"
    $  \b → MenuRequest
    <$> b .: "lesson"
    <*> b .: "score"
    <*> b .: "time"
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
  toJSON (ServerTree { .. }) = Aeson.object
    [ "sentence" .= sentence
    , "menu"     .= menu
    ]

serverTree ∷ Annotated → Menu → ServerTree
serverTree = ServerTree

data LoginSuccess = LoginSuccess Text

instance FromJSON LoginSuccess where
  parseJSON = Aeson.withObject "login-success"
    $ \ v →  LoginSuccess
    <$> v .: "token"

instance ToJSON LoginSuccess where
  toJSON (LoginSuccess token) = Aeson.object
    [ "login-succes" .= token
    ]

data LessonList = LessonList [Lesson2]

instance FromJSON LessonList where
  parseJSON = Aeson.withObject "lesson-list"
    $ \ v →  LessonList
    <$> v .: "lessons"

instance ToJSON LessonList where
  toJSON (LessonList lessons) = Aeson.object
    [ "lessons" .= lessons
    ]

data MenuList = MenuList
  { lesson  ∷ Text
  , passed  ∷ Bool
  , score   ∷ Score
  , src     ∷ ServerTree
  , trg     ∷ ServerTree
  }

instance FromJSON MenuList where
  parseJSON = Aeson.withObject "menu-list"
    $ \ o → MenuList
    <$> o .: "lesson"
    <*> o .: "passed"
    <*> o .: "clicks"
    <*> o .: "src"
    <*> o .: "trg"

instance ToJSON MenuList where
  toJSON MenuList{..} = Aeson.object
    [ "lesson"  .= lesson
    , "success" .= passed
    , "score"   .= score
    , "src"     .= src
    , "trg"     .= trg
    ]

data User = User
  { name     ∷ Text
  , password ∷ Text
  }

deriving stock instance Show User

instance FromJSON User where
  parseJSON = Aeson.withObject "user"
     $ \v -> User
    <$> v .: "name"
    <*> v .: "password"

-- | Like a 'User' but with an old and a new password.
data ChangePwd = ChangePwd
  { name        ∷ Text
  , oldPassword ∷ Text
  , newPassword ∷ Text
  }

deriving stock instance Show ChangePwd

instance FromJSON ChangePwd where
  parseJSON = Aeson.withObject "user"
     $ \v -> ChangePwd
    <$> v .: "name"
    <*> v .: "old-password"
    <*> v .: "new-password"
