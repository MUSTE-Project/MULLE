{-# language
    OverloadedStrings
  , TypeApplications
  , LambdaCase
#-}
module Ajax
  ( ServerTree(..)
  , ServerMessage(..)
  , ClientTree(..)
  , ClientMessage(..)
  , Menu(..)
  , Lesson(..)
  , decodeClientMessage
  ) where

import Data.Aeson hiding (Null,String)
import qualified Data.Aeson as A
import Data.Aeson.Types hiding (Null)
import Data.Text (Text(..),pack)
import qualified Data.Text as T
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.Map.Strict as Map
import qualified Data.Vector as V
import Data.Maybe
import Control.Exception

import Muste

data ClientMessageException = CME String deriving (Show)
data ReadTreeException = RTE String deriving (Show)

instance Exception ClientMessageException
instance Exception ReadTreeException

data ClientTree = ClientTree {
  clanguage :: String,
  ctree :: String
  } deriving (Show) ;

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
    , ctime :: Int
    , ca :: ClientTree
    , cb :: ClientTree
    }
  deriving (Show) ;

instance FromJSON ClientTree where
  parseJSON = withObject "ClientTree" $ \v -> ClientTree
    <$> v .: "grammar"
    <*> v .: "tree"

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

instance ToJSON ClientTree where
    -- this generates a Value
    toJSON (ClientTree tree language) =
      object [
      "tree" .= tree ,
      "language" .= language
      ]

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
    where
      (|>) = createMessageObject

data Menu = Menu (Map.Map Path [[CostTree]]) deriving (Show)

data ServerTree = ServerTree {
  slanguage :: String ,
  stree :: String,
  slin :: [LinToken] ,
  smenu :: Menu
  } deriving (Show) ;

data Lesson = Lesson {
  lname :: String,
  ldescription :: String,
  lexercisecount :: Int,
  lpassedcount :: Int,
  lscore :: Int,
  ltime :: Int,
  lfinished :: Bool,
  lenabled :: Bool
  } deriving Show;

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

instance FromJSON Menu where
  parseJSON = withObject "CostTree" $ \v -> Menu
    <$> v .: "menu"

instance FromJSON ServerTree where
  parseJSON = withObject "ServerTree" $ \v -> ServerTree
    <$> v .: "grammar"
    <*> v .: "tree"
    <*> v .: "lin"
    <*> v .: "menu"

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
        }

instance ToJSON Menu where
    toJSON (Menu map) =
      object [ (pack $ show k) .= (Map.!) map  k | k <- Map.keys map]

instance ToJSON ServerTree where
    -- this generates a Value
    toJSON (ServerTree grammar tree lin menu) =
      object [
      "grammar" .= grammar ,
      "tree" .= tree ,
      "lin" .= lin ,
      "menu" .= menu]

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

-- FIXME Indicate in type signature that we can fail (e.g. `IO
-- ClientMessage`)
decodeClientMessage :: B.ByteString -> ClientMessage
decodeClientMessage s =
  let rcm = eitherDecode @ClientMessage s
  in
    either (throw . CME) id rcm
