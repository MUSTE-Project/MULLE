module Ajax where

import Data.Aeson hiding (Null,String)
import qualified Data.Aeson as A
import Data.Aeson.Types hiding (Null)

import Data.Text (Text(..),pack,unpack)
import qualified Data.Text as T

import qualified Data.ByteString.Lazy.Char8 as B

import Data.Monoid

import qualified Data.Map.Strict as Map
import Data.Map hiding (map)

import qualified Data.Vector as V

import Data.List

import Data.Maybe

import Muste.Tree
-- import Muste

-- import Debug.Trace

import Control.Exception

data ClientMessageException = CME String deriving (Show)
data ReadTreeException = RTE String deriving (Show)

instance Exception ClientMessageException
instance Exception ReadTreeException


data ClientTree = CT {
  clanguage :: String,
  ctree :: String
  } deriving (Show) ;

createMessageObject :: String -> Value -> Value
createMessageObject msg params =
  object [
  T.pack "message" .= (A.String $ T.pack msg) ,
  T.pack "parameters" .= params
  ]
  
data ClientMessage = CMNull
                   | CMLoginRequest {
                       cusername :: String ,
                       cpassword :: String
                       }
                   | CMMOTDRequest { ctoken :: String }
                   | CMDataResponse {
                       ctoken :: String,
                       context :: String,
                       cdata :: [(String, String)]
                       }
                   | CMLessonsRequest { ctoken :: String }
                   | CMLessonInit {
                       ctoken :: String,
                       clesson :: String
                       }
                   | CMMenuRequest {
                       ctoken :: String,
                       clesson :: String,
                       cscore :: Int ,
                       ctime :: Int , 
                       ca :: ClientTree ,
                       cb :: ClientTree
                       }
                   deriving (Show) ;
  
instance FromJSON ClientTree where
  parseJSON = withObject "ClientTree" $ \v -> CT
    <$> v .: T.pack "grammar"
    <*> v .: T.pack "tree"
    
instance FromJSON ClientMessage where
  parseJSON =
    withObject "ClientMessage" $ \v ->
    do
      msg <- v .: T.pack "message" :: Parser Text
      params <- v .: T.pack "parameters" :: Parser Object
      case T.unpack $ msg of {
        "CMLoginRequest" ->
            CMLoginRequest
            <$> params .: T.pack "username"
            <*> params .: T.pack "password" ;
        "CMMOTDRequest" ->
            CMMOTDRequest
            <$> params .: T.pack "token" ;
        "CMDataResponse" ->
            (do
                ctoken <- params .: T.pack "token"
                ccontext <- params .: T.pack "context"
                cdata <- params .: T.pack "data"  :: Parser Value
                carray <- case cdata of {
                  Array a -> sequence $ V.toList $ V.map (withObject "Key-Value-Pair" $ \o -> do
                                                             f <- o .: T.pack "field"
                                                             v <- o .: T.pack "value"
                                                             return (f,v)
                                                         ) a ;
                    _ -> error "Boo, not an array"
                  }
                return $ CMDataResponse ctoken ccontext carray
            );
            -- (o .: T.pack "field", o .: T.pack "value")
        "CMLessonsRequest" -> 
            CMLessonsRequest
            <$> params .: T.pack "token" ;
        "CMLessonInit" -> 
            CMLessonInit
            <$> params .: T.pack "token"
            <*> params .: T.pack "lesson" ;
        "CMMenuRequest" -> 
            CMMenuRequest
             <$> params .: T.pack "token"
             <*> params .: T.pack "lesson"
             <*> params .: T.pack "score"
             <*> params .: T.pack "time"
             <*> params .: T.pack "a"
             <*> params .: T.pack "b"             
         }

instance ToJSON ClientTree where
    -- this generates a Value
    toJSON (CT tree language) =
      object [
      T.pack "tree" .= tree ,
      T.pack "language" .= language
      ]

instance ToJSON ClientMessage where
    -- this generates a Value
  toJSON (CMLoginRequest username password) =
    createMessageObject "CMLoginRequest" $ object [
    T.pack "username" .= username ,
    T.pack "password" .= password
    ]
  toJSON (CMMOTDRequest token) =
    createMessageObject "CMMOTDRequest" $ object [
    T.pack "token" .= token
    ]
  toJSON (CMDataResponse token context cdata) =
    createMessageObject "CMDataResponse" $ object [
    T.pack "token" .= token ,
    T.pack "context" .= context ,
    T.pack "data" .= map (\(k,v) -> object [ T.pack "field" .= k, T.pack "value" .= v ]) cdata
    ]
  toJSON (CMMenuRequest token lesson score time a b) =
    createMessageObject "CMMenuRequest" $ object [
    T.pack "token" .= token ,
    T.pack "lesson" .= lesson ,
    T.pack "score" .= score ,
    T.pack "time" .= time ,
    T.pack "a" .= a ,
    T.pack "b" .= b
    ]

     
      
--data CostTree = T { cost :: Int , lin :: String , tree :: String } deriving (Show)

data LinToken = LinToken { ltpath :: Path, ltlin :: String, ltmatched :: Bool } deriving (Show)
data Linearization = Linearization { ltpath :: Path, ltlin :: String } deriving (Show)
data CostTree = CostTree { cost :: Int , lin :: Linearization , tree :: String } deriving (Show)
-- lin is the full linearization

--data Menu = M (Map.Map (Int,Int) [[CostTree]]) deriving (Show)
data Menu = Menu (Map.Map Path [[CostTree]]) deriving (Show)

data ServerTree = ServerTree {
  slanguage :: String ,
  stree :: String,
  slin :: LinToken ,
  smenu :: Menu
  } deriving (Show) ;

data Lesson = Lesson {
  lname :: String,
  ldescription :: String,
  lexercises :: Int,
  lpassed :: Bool
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
                   deriving (Show) ;

instance FromJSON LinToken where
  parseJSON = withObject "LinToken" $ \v -> LinToken
    <$> v .: T.pack "path"
    <*> v .: T.pack "lin"
    <*> v .: T.pack "matched"
instance FromJSON CostTree where
  parseJSON = withObject "CostTree" $ \v -> CostTree
    <$> v .: T.pack "cost"
    <*> v .: T.pack "lin"
    <*> v .: T.pack "tree"

instance FromJSON Menu where
  parseJSON = withObject "CostTree" $ \v -> Menu
    <$> v .: T.pack "menu"
    
instance FromJSON ServerTree where
  parseJSON = withObject "ServerTree" $ \v -> ServerTree
    <$> v .: T.pack "grammar"
    <*> v .: T.pack "tree"
    <*> v .: T.pack "lin"
    <*> v .: T.pack "menu"

instance FromJSON Lesson where
  parseJSON = withObject "Lesson" $ \v -> Lesson
    <$> v .: T.pack "name"
    <*> v .: T.pack "description"
    <*> v .: T.pack "exercises"
    <*> v .: T.pack "passed"
instance FromJSON ServerMessage where
  parseJSON = withObject "ServerMessage" $ \v ->
    do
      msg <- v .: T.pack "message" :: Parser Text
      params <- v .:? T.pack "parameters" :: Parser (Maybe Object)
      case T.unpack $ msg of {
        "SMLoginSuccess" ->
            SMLoginSuccess <$> fromJust params .: T.pack "token" ;
        "SMLoginFail" -> return SMLoginFail ;
        "SMMOTDResponse" ->
            SMMOTDResponse <$> fromJust params .: T.pack "filename" ;
        "SMSessionInvalid" ->
            SMSessionInvalid <$> fromJust params .: T.pack "error" ;
        "SMLessonsList" ->
            (do
              clist <- fromJust params .: T.pack "lessons"
              return $ SMLessonsList clist
            ) ;
        "SMMenuList" -> SMMenuList
            <$> fromJust params .: T.pack "success"
            <*> fromJust params .: T.pack "score"
            <*> fromJust params .: T.pack "a"
            <*> fromJust params .: T.pack "b" ;
        "SMLessonInvalid" -> return SMLessonInvalid ;
        "SMDataReceived" -> return SMDataReceived ;
        "SMDataInvalid" ->
            SMDataInvalid <$> fromJust params .: T.pack "error" ;
        }

instance ToJSON LinToken where
  toJSON (LinToken path lin matched) =
    object [
    T.pack "path" .= path ,
    T.pack "lin" .= lin ,
    T.pack "matched" .= matched
    ]

instance ToJSON CostTree where
    -- this generates a Value
    toJSON (CostTree score lin tree) =
      object [
      T.pack "score" .= score ,
      T.pack "lin" .= lin ,
      T.pack "tree" .= tree
      ]

instance ToJSON Menu where
    toJSON (Menu map) =
      object [ (pack $ show k) .= (Map.!) map  k | k <- Map.keys map]

instance ToJSON ServerTree where
    -- this generates a Value
    toJSON (ServerTree grammar tree lin menu) =
      object [
      T.pack "grammar" .= grammar ,
      T.pack "tree" .= tree ,
      T.pack "lin" .= lin ,
      T.pack "menu" .= menu]

instance ToJSON Lesson where
  toJSON (Lesson name description exercises passed) =
    object [
    T.pack "name" .= name,
    T.pack "description" .= description ,
    T.pack "exercises" .= exercises ,
    T.pack "passed" .= passed
    ]


instance ToJSON ServerMessage where
    -- this generates a Value
  toJSON (SMLoginSuccess stoken) =
    createMessageObject "SMLoginSuccess" $ object [
    T.pack "token" .= (String $ T.pack stoken)
    ]
  toJSON SMLoginFail =
    createMessageObject "SMLoginFail" A.Null
  toJSON (SMMOTDResponse sfilename) =
    createMessageObject "SMMOTDRequest" $ object [
    T.pack "filename" .= (String $ T.pack sfilename)
    ]
  toJSON (SMSessionInvalid error) =
    createMessageObject "SMSessionInvalid" $ object [
    T.pack "error" .= (String $ T.pack error)
    ]
  toJSON (SMLessonsList slessons) =
    createMessageObject "SMLessonsList" $ object [
    T.pack "lessons" .= toJSON slessons 
    ]
  toJSON (SMMenuList ssuccess sscore sa sb) =
    createMessageObject "SMMenuList" $ object [
    T.pack "success" .= ssuccess ,
    T.pack "score" .= sscore ,
    T.pack "a" .= sa ,
    T.pack "b" .= sb
    ]
  toJSON SMLessonInvalid =
    createMessageObject "SMLessonInvalid" A.Null
  toJSON SMDataReceived =
    createMessageObject "SMDataReceived" A.Null
  toJSON (SMDataInvalid error) =
    createMessageObject "SMDataInvalid" $ object [
    T.pack "error" .= (String $ T.pack error)
    ]

decodeClientMessage :: String -> ClientMessage
decodeClientMessage s =
  let rcm = eitherDecode (B.pack s) :: Either String ClientMessage
  in
    either (throw . CME) id rcm

encodeServerMessage :: ServerMessage -> String
encodeServerMessage sm =
  B.unpack $ encode sm
