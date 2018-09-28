{-# OPTIONS_GHC -Wall #-}
{-# language OverloadedStrings, DuplicateRecordFields , RecordWildCards,
  NamedFieldPuns #-}
module Ajax
  ( ServerTree
  , ServerMessage(..)
  , ClientTree(ClientTree)
  , ClientMessage(..)
  , Lesson2(..)
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
  | CMMenuRequest
    { lesson :: Text
    , score :: Integer
    , time :: NominalDiffTime
    , a :: ClientTree
    , b :: ClientTree
    }
  deriving (Show)

instance FromJSON ClientMessage where
  parseJSON = withObject "ClientMessage" $ \v -> do
    msg <- v .: "message" :: Parser Text
    params <- v .: "parameters" :: Parser Object
    case msg of
      "login" -> CMLoginRequest <$> params .: "username" <*> params .: "password"
      "lesson" -> CMLessonInit <$> params .: "lesson"
      "menu" -> CMMenuRequest
        <$> params .: "lesson"
        <*> params .: "score"
        <*> params .: "time"
        <*> params .: "a"
        <*> params .: "b"
      _ -> fail $ "Unexpected message " <> show v

instance ToJSON ClientMessage where
  toJSON = \case
    (CMLoginRequest username password) -> "CMLoginRequest" |> object
      [ "username" .= username
      , "password" .= password
      ]
    (CMMenuRequest lesson score time a b) -> "CMMenuRequest" |> object
      [ "lesson" .= lesson
      , "score"  .= score
      , "time"   .= time
      , "a"      .= a
      , "b"      .= b
      ]
    _ → error "Ajax.toJSON @ClientMessage: Non-exhaustive pattern-match"
    where
      (|>) = createMessageObject

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
  | SMMenuList
    { slesson :: Text
    , spassed :: Bool
    , sclicks :: Integer
    , sa      :: ServerTree
    , sb      :: ServerTree
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
        "SMMenuList" -> SMMenuList
            <$> fromJust params .: "lesson"
            <*> fromJust params .: "passed"
            <*> fromJust params .: "clicks"
            <*> fromJust params .: "a"
            <*> fromJust params .: "b" ;
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
  toJSON (SMMenuList slesson spassed sclicks sa sb) =
    createMessageObject "SMMenuList" $ object [
    "lesson" .= slesson,
    "success" .= spassed ,
    "score" .= sclicks ,
    "a" .= sa ,
    "b" .= sb
    ]
