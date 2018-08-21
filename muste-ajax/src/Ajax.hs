{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}
{-# language OverloadedStrings, DuplicateRecordFields #-}
module Ajax
  ( ServerTree
  , ServerMessage(..)
  , ClientTree(ClientTree)
  , ClientMessage(CMMenuRequest, CMLoginRequest)
  , Menu
  , Lesson(..)
  , decodeClientMessage
  , mkServerTree
  , lessonFromTuple
  ) where

import Data.Aeson hiding (Null,String)
import qualified Data.Aeson as A
import Data.Aeson.Types hiding (Null)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.Vector as V
import Data.Maybe
import Control.Exception
import Data.Time

import Muste

data ClientMessageException = CME String deriving (Show)
data ReadTreeException = RTE String deriving (Show)

instance Exception ClientMessageException
instance Exception ReadTreeException

data ClientTree = ClientTree
  { clanguage ∷ String
  , lin       ∷ Linearization
  } deriving (Show)

instance FromJSON ClientTree where
  parseJSON = withObject "tree"
     $ \v -> ClientTree
    <$> v .: "grammar"
    <*> v .: "lin"

instance ToJSON ClientTree where
  toJSON (ClientTree tree language) = object
    [ "trees"     .= tree
    , "language"  .= language
    ]

createMessageObject :: String -> Value -> Value
createMessageObject msg params =
  object [
  "message" .= msg ,
  "parameters" .= params
  ]

data ClientMessage
  = CMLoginRequest
    { cusername :: T.Text
    , cpassword :: T.Text
    }
  | CMMOTDRequest
  | CMDataResponse
    { context :: String
    , cdata :: [(String, String)]
    }
  | CMLessonInit
    { clesson :: T.Text
    }
  | CMMenuRequest
    { clesson :: T.Text
    , cscore :: Integer
    , ctime :: NominalDiffTime
    , ca :: ClientTree
    , cb :: ClientTree
    }
  deriving (Show)

instance FromJSON ClientMessage where
  parseJSON = withObject "ClientMessage" $ \v -> do
    msg <- v .: "message" :: Parser Text
    params <- v .: "parameters" :: Parser Object
    case msg of
      "login" -> CMLoginRequest <$> params .: "username" <*> params .: "password"
      "CMMOTDRequest" -> pure CMMOTDRequest
      "CMDataResponse" -> do
        ccontext <- params .: "context"
        cdata <- params .: "data"  :: Parser Value
        carray <- case cdata of
          Array a -> sequence
            $ V.toList
            $ V.map (withObject "Key-Value-Pair" $ \o -> do
                                                     f <- o .: "field"
                                                     v <- o .: "value"
                                                     return (f,v)
                                                 ) a ;
            _ -> error "Boo, not an array"
        return $ CMDataResponse ccontext carray
          -- (o .: "field", o .: "value")
      "lesson" -> CMLessonInit <$> params .: "lesson"
      "menu" -> CMMenuRequest
        <$> params .: "lesson"
        <*> params .: "score"
        <*> params .: "time"
        <*> params .: "a"
        <*> params .: "b"
      _ -> error ( "Unexpected message " ++ show v)

instance ToJSON ClientMessage where
  toJSON = \case
    (CMLoginRequest username password) -> "CMLoginRequest" |> object
      [ "username" .= username
      , "password" .= password
      ]
    CMMOTDRequest -> "CMMOTDRequest" |> object []
    (CMDataResponse context cdata) -> "CMDataResponse" |> object
      [ "context" .= context
      , "data" .= map (\(k,v) -> object [ "field" .= k, "value" .= v ]) cdata
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
  { slanguage ∷ String
  , lin       ∷ Linearization
  , smenu     ∷ Menu
  } deriving (Show)

instance FromJSON ServerTree where
  parseJSON = withObject "ServerTree" $ \v -> ServerTree
    <$> v .: "grammar"
    <*> v .: "lin"
    <*> v .: "menu"

instance ToJSON ServerTree where
  toJSON (ServerTree grammar lin menu) = object
    [ "grammar" .= grammar
    , "lin"     .= lin
    , "menu"    .= menu
    ]

mkServerTree ∷ String → Linearization → Menu → ServerTree
mkServerTree lang lin menu = ServerTree lang lin menu

data Lesson = Lesson {
  lname :: Text,
  ldescription :: Text,
  lexercisecount :: Int,
  lpassedcount :: Int,
  lscore :: Int,
  ltime :: NominalDiffTime,
  lfinished :: Bool,
  lenabled :: Bool
  } deriving Show;

lessonFromTuple
  :: (Text,Text,Int,Int,Int,NominalDiffTime,Bool,Bool)
  -> Lesson
lessonFromTuple
  ( name, description, exercises
  , passedcount, score, time
  , passed, enabled
  ) = Lesson
    name description exercises
    passedcount score time passed enabled

data ServerMessage = SMNull
                   | SMLoginSuccess { stoken :: T.Text }
                   | SMLoginFail
                   | SMMOTDResponse { sfilename :: String }
                   | SMSessionInvalid { serror :: String }
                   | SMLessonsList { slessions :: [Lesson] }
                   | SMMenuList {
                       slesson :: T.Text ,
                       spassed :: Bool ,
                       sclicks :: Integer ,
                       sa :: ServerTree ,
                       sb :: ServerTree
                       }
                   | SMLessonInvalid
                   | SMDataReceived
                   | SMDataInvalid { serror :: String }
                   | SMLogoutResponse
                   deriving (Show) ;

instance FromJSON Lesson where
  parseJSON = withObject "Lesson" $ \v -> Lesson
    <$> v .: "name"
    <*> v .: "description"
    <*> v .: "exercisecount"
    <*> v .: "passedcount"
    <*> v .: "score"
    <*> v .: "time"
    <*> v .: "passed"
    <*> v .: "enabled"

instance FromJSON ServerMessage where
  parseJSON = withObject "ServerMessage" $ \v ->
    do
      msg <- v .: "message" :: Parser Text
      params <- v .:? "parameters" :: Parser (Maybe Object)
      case T.unpack msg of {
        "SMLoginSuccess" ->
            SMLoginSuccess <$> fromJust params .: "token" ;
        "SMLoginFail" -> return SMLoginFail ;
        "SMMOTDResponse" ->
            SMMOTDResponse <$> fromJust params .: "filename" ;
        "SMSessionInvalid" ->
            SMSessionInvalid <$> fromJust params .: "error" ;
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
        "SMLessonInvalid" -> return SMLessonInvalid ;
        "SMDataReceived" -> return SMDataReceived ;
        "SMDataInvalid" ->
            SMDataInvalid <$> fromJust params .: "error" ;
        "SMLogoutResponse" -> return SMLogoutResponse ;
        _ → error "Ajax.parseJSON @ServerMessage: Non-exhaustive pattern match"
        }

instance ToJSON Lesson where
  toJSON (Lesson name description exercises passedcount score time passed enabled) =
    object [
    "name" .= name,
    "description" .= description ,
    "exercisecount" .= exercises ,
    "passedcount" .= passedcount ,
    "score" .= score,
    "time" .= time,
    "passed" .= passed,
    "enabled" .= enabled
    ]


instance ToJSON ServerMessage where
    -- this generates a Value
  toJSON (SMLoginSuccess stoken) =
    createMessageObject "SMLoginSuccess" $ object [
    "token" .= stoken
    ]
  toJSON SMLoginFail =
    createMessageObject "SMLoginFail" A.Null
  toJSON (SMMOTDResponse sfilename) =
    createMessageObject "SMMOTDRequest" $ object [
    "filename" .= sfilename
    ]
  toJSON (SMSessionInvalid error) =
    createMessageObject "SMSessionInvalid" $ object [
    "error" .= error
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
  toJSON SMLessonInvalid =
    createMessageObject "SMLessonInvalid" A.Null
  toJSON SMDataReceived =
    createMessageObject "SMDataReceived" A.Null
  toJSON (SMDataInvalid error) =
    createMessageObject "SMDataInvalid" $ object [
    "error" .= error
    ]
  toJSON SMLogoutResponse =
    createMessageObject "SMLogoutResponse" A.Null
  toJSON _ = error "Ajax.toJSON @ServerMessage: Non-exhaustive pattern match"

-- FIXME Indicate in type signature that we can fail (e.g. `IO
-- ClientMessage`)
decodeClientMessage :: B.ByteString -> ClientMessage
decodeClientMessage s =
  let rcm = eitherDecode @ClientMessage s
  in
    either (throw . CME) id rcm
