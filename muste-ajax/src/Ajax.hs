{-# LANGUAGE OverloadedStrings #-}
module Ajax
  ( ServerTree(..)
  , ServerMessage(..)
  , ClientTree(..)
  , ClientMessage(..)
  , Menu(..)
  , encodeServerMessage
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
import Muste.Tree
import Muste.Linearization (LinToken)

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
  = CMNull
  | CMLoginRequest
    { cusername :: String
    , cpassword :: String
    }
  | CMMOTDRequest
    { ctoken :: String
    }
  | CMDataResponse
    { ctoken :: String
    , context :: String
    , cdata :: [(String, String)]
    }
  | CMLessonsRequest
    { ctoken :: String
    }
  | CMLessonInit
    { ctoken :: String
    , clesson :: String
    }
  | CMMenuRequest
    { ctoken :: String
    , clesson :: String
    , cscore :: Int
    , ctime :: Int
    , ca :: ClientTree
    , cb :: ClientTree
    }
  | CMLogoutRequest
    { ctoken :: String
    }
  deriving (Show) ;

instance FromJSON ClientTree where
  parseJSON = withObject "ClientTree" $ \v -> ClientTree
    <$> v .: "grammar"
    <*> v .: "tree"

instance FromJSON ClientMessage where
  parseJSON =
    withObject "ClientMessage" $ \v ->
    do
      msg <- v .: "message" :: Parser Text
      params <- v .: "parameters" :: Parser Object
      case msg of {
        "CMLoginRequest" ->
            CMLoginRequest
            <$> params .: "username"
            <*> params .: "password" ;
        "CMMOTDRequest" ->
            CMMOTDRequest
            <$> params .: "token" ;
        "CMDataResponse" ->
            (do
                ctoken <- params .: "token"
                ccontext <- params .: "context"
                cdata <- params .: "data"  :: Parser Value
                carray <- case cdata of {
                  Array a -> sequence $ V.toList $ V.map (withObject "Key-Value-Pair" $ \o -> do
                                                             f <- o .: "field"
                                                             v <- o .: "value"
                                                             return (f,v)
                                                         ) a ;
                    _ -> error "Boo, not an array"
                  }
                return $ CMDataResponse ctoken ccontext carray
            );
            -- (o .: "field", o .: "value")
        "CMLessonsRequest" ->
            CMLessonsRequest
            <$> params .: "token" ;
        "CMLessonInit" ->
            CMLessonInit
            <$> params .: "token"
            <*> params .: "lesson" ;
        "CMMenuRequest" ->
            CMMenuRequest
             <$> params .: "token"
             <*> params .: "lesson"
             <*> params .: "score"
             <*> params .: "time"
             <*> params .: "a"
             <*> params .: "b" ;
        "CMLogoutRequest" ->
            CMLogoutRequest
            <$> params .: "token" ;
        _ -> error ( "Unexpected message " ++ show v)
         }

instance ToJSON ClientTree where
    -- this generates a Value
    toJSON (ClientTree tree language) =
      object [
      "tree" .= tree ,
      "language" .= language
      ]

instance ToJSON ClientMessage where
    -- this generates a Value
  toJSON (CMLoginRequest username password) =
    createMessageObject "CMLoginRequest" $ object [
    "username" .= username ,
    "password" .= password
    ]
  toJSON (CMMOTDRequest token) =
    createMessageObject "CMMOTDRequest" $ object [
    "token" .= token
    ]
  toJSON (CMDataResponse token context cdata) =
    createMessageObject "CMDataResponse" $ object [
    "token" .= token ,
    "context" .= context ,
    "data" .= map (\(k,v) -> object [ "field" .= k, "value" .= v ]) cdata
    ]
  toJSON (CMMenuRequest token lesson score time a b) =
    createMessageObject "CMMenuRequest" $ object [
    "token" .= token ,
    "lesson" .= lesson ,
    "score" .= score ,
    "time" .= time ,
    "a" .= a ,
    "b" .= b
    ]
  toJSON (CMLogoutRequest token) =
    createMessageObject "CMLogoutRequest" $ object [
    "token" .= token
    ]


--data Menu = M (Map.Map (Int,Int) [[CostTree]]) deriving (Show)
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
                   | SMLoginSuccess { stoken :: String }
                   | SMLoginFail
                   | SMMOTDResponse { sfilename :: String }
                   | SMSessionInvalid { serror :: String }
                   | SMLessonsList { slessions :: [Lesson] }
                   | SMMenuList {
                       slesson :: String ,
                       spassed :: Bool ,
                       sclicks :: Int ,
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

decodeClientMessage :: String -> ClientMessage
decodeClientMessage s =
  let rcm = eitherDecode (B.pack s) :: Either String ClientMessage
  in
    either (throw . CME) id rcm

encodeServerMessage :: ServerMessage -> String
encodeServerMessage sm =
  B.unpack $ encode sm
