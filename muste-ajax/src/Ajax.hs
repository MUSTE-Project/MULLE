{-# OPTIONS_GHC -Wall #-}
{-# language OverloadedStrings, DuplicateRecordFields , RecordWildCards,
  NamedFieldPuns #-}
module Ajax
  ( ServerTree
  , ServerMessage(..)
  , ClientTree(ClientTree)
  , ClientMessage(..)
  , Lesson2(..)
  , User(..)
  , ChangePwd(..)
  , MenuRequest(..)
  , MenuList(..)
  , serverTree
  , unClientTree
  ) where

import Prelude ()
import Muste.Prelude

import Data.Aeson
  ( parseJSON, toJSON, Value, Object, withObject, (.:), object, (.=)
  , (.:?)
  )
import Data.Aeson.Types (Parser)
import Data.Text (Text)
import Data.Time

import Muste
import Muste.Sentence.Unannotated (Unannotated)
import Muste.Sentence.Annotated (Annotated)

import Database (Lesson2(..))

newtype ClientTree = ClientTree { unClientTree ∷ Unannotated }

deriving instance Show ClientTree

instance FromJSON ClientTree where
  parseJSON = withObject "tree"
     $ \v -> ClientTree
    <$> v .: "sentence"

instance ToJSON ClientTree where
  toJSON (ClientTree sentence) = object
    [ "sentence" .= sentence
    ]

createMessageObject :: String -> Value -> Value
createMessageObject msg params = object
  [ "message"    .= msg
  , "parameters" .= params
  ]

data ClientMessage
  = CMLoginRequest
    { username :: Text
    , password :: Text
    }
  | CMLessonInit
    { lesson :: Text
    }
  deriving (Show)

instance FromJSON ClientMessage where
  parseJSON = withObject "ClientMessage" $ \v -> do
    msg <- v .: "message" :: Parser Text
    params <- v .: "parameters" :: Parser Object
    case msg of
      "login" -> CMLoginRequest <$> params .: "username" <*> params .: "password"
      "lesson" -> CMLessonInit <$> params .: "lesson"
      _ -> fail $ "Unexpected message " <> show v

instance ToJSON ClientMessage where
  toJSON = \case
    (CMLoginRequest username password) -> "CMLoginRequest" |> object
      [ "username" .= username
      , "password" .= password
      ]
    _ → error "Ajax.toJSON @ClientMessage: Non-exhaustive pattern-match"
    where
      (|>) = createMessageObject

data MenuRequest = MenuRequest
  { lesson ∷ Text
  , score  ∷ Integer
  , time   ∷ NominalDiffTime
  , src    ∷ ClientTree
  , trg    ∷ ClientTree
  }

instance ToJSON MenuRequest where
  toJSON MenuRequest{..} = object
    [ "lesson" .= lesson
    , "score"  .= score
    , "time"   .= time
    , "src"    .= src
    , "trg"    .= trg
    ]

instance FromJSON MenuRequest where
  parseJSON = withObject "menu-request"
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
  parseJSON = withObject "server-tree" $ \v -> ServerTree
    <$> v .: "sentence"
    <*> v .: "menu"

instance ToJSON ServerTree where
  toJSON (ServerTree { .. }) = object
    [ "sentence" .= sentence
    , "menu"     .= menu
    ]

serverTree ∷ Annotated → Menu → ServerTree
serverTree = ServerTree

data ServerMessage
  = SMLoginSuccess
    { stoken :: Text
    }
  | SMLessonsList
    { slessions :: [Lesson2]
    }

instance FromJSON ServerMessage where
  parseJSON = withObject "ServerMessage" $ \v ->
    do
      msg <- v .: "message" :: Parser Text
      params <- v .:? "parameters" :: Parser (Maybe Object)
      case msg of
        "SMLoginSuccess" ->
            SMLoginSuccess <$> fromJust params .: "token" ;
        "SMLessonsList" ->
            (do
              clist <- fromJust params .: "lessons"
              return $ SMLessonsList clist
            ) ;
        _ → fail "Unknown message"

instance ToJSON ServerMessage where
    -- this generates a Value
  toJSON (SMLoginSuccess stoken) =
    createMessageObject "SMLoginSuccess" $ object [
    "token" .= stoken
    ]
  toJSON (SMLessonsList slessons) =
    createMessageObject "SMLessonsList" $ object [
    "lessons" .= toJSON slessons
    ]

data MenuList = MenuList
  { lesson  ∷ Text
  , passed  ∷ Bool
  , clicks  ∷ Integer
  , src     ∷ ServerTree
  , trg     ∷ ServerTree
  }

instance FromJSON MenuList where
  parseJSON = withObject "menu-list"
    $ \ o → MenuList
    <$> o .: "lesson"
    <*> o .: "passed"
    <*> o .: "clicks"
    <*> o .: "src"
    <*> o .: "trg"

instance ToJSON MenuList where
  toJSON MenuList{..} = object
    [ "lesson"  .= lesson
    , "success" .= passed
    , "score"   .= clicks
    , "src"     .= src
    , "trg"     .= trg
    ]

data User = User
  { name     ∷ Text
  , password ∷ Text
  }

deriving stock instance Show User

instance FromJSON User where
  parseJSON = withObject "user"
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
  parseJSON = withObject "user"
     $ \v -> ChangePwd
    <$> v .: "name"
    <*> v .: "old-password"
    <*> v .: "new-password"
