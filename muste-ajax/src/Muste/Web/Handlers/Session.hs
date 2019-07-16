{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language
 GeneralizedNewtypeDeriving,
 NamedFieldPuns,
 OverloadedStrings,
 ScopedTypeVariables
#-}

module Muste.Web.Handlers.Session
  ( loginUser
  , logoutUser
  , createUser
  , changePwd
  , getAllLessons
  , getAllCourses
  , Token
  , Empty
  , SessionToken(..)
  , SessionTokenOnly(..)
  , verifySession
  , addUser
  ) where

import Control.Monad (when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (asks)
import qualified Control.Exception.Lifted as CL

import qualified Database.SQLite.Simple as SQL
import Database.SQLite.Simple (NamedParam((:=)))
import Database.SQLite.Simple.FromField (FromField)
import Database.SQLite.Simple.ToField (ToField)

import Data.Aeson ((.=), (.:), FromJSON(parseJSON), ToJSON(toJSON))
import qualified Data.Aeson as Aeson
import Data.Yaml (decodeFileThrow)
import qualified Data.Text.Encoding as Enc
import Data.Text (Text)
import qualified Data.Text as Text
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as ByteString
import qualified Data.Time.Clock as Time
import qualified Data.Time.Format as Time
import Data.Time.Clock (UTCTime)
import Data.Time (NominalDiffTime)

import qualified Crypto.Random as CryptoR
import qualified Crypto.KDF.PBKDF2 as CryptoK
import qualified Crypto.Hash as CryptoH

import Muste.Web.Config (Course(..))
import qualified Muste.Web.Class as MULLError (MULLError(..))
import Muste.Web.Class (MULLE, wrapConnection, AppState(courses))



--------------------------------------------------------------------------------
-- /login, create-user

loginUser :: NamePwd -> MULLE v SessionTokenOnly
loginUser (NamePwd name pwd) = wrapConnection $ \conn -> 
  do authUser conn name pwd
     token <- startSession conn name
     return (SessionTokenOnly token)

createUser :: NamePwd -> MULLE v ()
createUser (NamePwd name pwd) = wrapConnection $ \conn -> 
    addUser conn name pwd


data NamePwd = NamePwd Text Text

instance FromJSON NamePwd where
  parseJSON = Aeson.withObject "NamePwd" $ \v -> NamePwd
    <$> v .: "name"
    <*> v .: "pwd"

instance ToJSON NamePwd where
  toJSON (NamePwd name pwd) = Aeson.object
    [ "name" .= name
    , "pwd"  .= pwd
    ]


--------------------------------------------------------------------------------
-- /change-pwd

changePwd :: NameOldNewPwd -> MULLE v ()
changePwd (NameOldNewPwd name oldpwd newpwd) = wrapConnection $ \conn -> 
  do authUser conn name oldpwd
     rmUser conn name
     addUser conn name newpwd


data NameOldNewPwd = NameOldNewPwd Text Text Text

instance FromJSON NameOldNewPwd where
  parseJSON = Aeson.withObject "NameOldNewPwd" $ \v -> NameOldNewPwd
    <$> v .: "name"
    <*> v .: "oldpwd"
    <*> v .: "newpwd"

instance ToJSON NameOldNewPwd where
  toJSON (NameOldNewPwd name oldpwd newpwd) = Aeson.object
    [ "name"   .= name
    , "oldpwd" .= oldpwd
    , "newpwd" .= newpwd
    ]


--------------------------------------------------------------------------------
-- /logout

logoutUser :: SessionTokenOnly -> MULLE v ()
logoutUser (SessionTokenOnly token) = wrapConnection $ \conn -> 
    deleteSession conn token


--------------------------------------------------------------------------------
-- /courses & lessons

getAllCourses :: SessionTokenOnly -> MULLE v [Text]
getAllCourses (SessionTokenOnly token)
  = do verifySession token
       theCourses <- asks courses
       return [ name | Course name _path <- theCourses ]


getAllLessons :: SessionToken Empty -> MULLE v Aeson.Value
getAllLessons (SessionToken token course _)
  = do verifySession token
       theCourses <- asks courses
       let lessonFiles = [ path | Course course' path <- theCourses, course == course' ]
       if null lessonFiles then 
          CL.throwIO $ MULLError.CourseNotFound course
       else
          do let lessonsFile = head lessonFiles
             liftIO $ putStrLn $ ">> Reading lessons file for course " ++ Text.unpack course ++ ": " ++ lessonsFile
             decodeFileThrow lessonsFile


data Empty = Empty
instance FromJSON Empty where 
  parseJSON = Aeson.withObject "Empty" $ \v -> return Empty
instance ToJSON Empty where
  toJSON Empty = Aeson.object []
           
--------------------------------------------------------------------------------
-- Database operations: users

-- | Adds an new user to the database.
addUser :: SQL.Connection -> Text -> Text -> IO ()
addUser conn name password 
  = do salt <- createSalt
       -- TODO: first ask the DB if the user exists instead of catching
       userList <- SQL.queryNamed conn 
         " SELECT Username FROM User WHERE Username = :Username "
         [ ":Username"  := name ]
       if not (null (userList :: [[Text]]))
         then CL.throwIO $ MULLError.UserAlreadyExists name
         else SQL.executeNamed conn
              " INSERT INTO User (Username, Password, Salt) \
              \ VALUES (:Username, :Password, :Salt) "
              [ ":Username"  := name
              , ":Password"  := hashPassword password salt
              , ":Salt"      := salt
              ]


-- | Removes an existing user from the database.
rmUser :: SQL.Connection -> Text -> IO ()
rmUser conn user
  = SQL.executeNamed conn
    " DELETE FROM User WHERE Username = :User "
    [ ":User" := user ]


-- | Authorizes an existing user.
authUser :: SQL.Connection -> Text -> Text -> IO ()
authUser conn user password 
  = do -- Get password and salt from database
       userList <- SQL.queryNamed conn 
         " SELECT Password, Salt \
         \ FROM User WHERE Username = :Username "
         [":Username" := user]
       -- Generate new password hash and compare to the stored one
       let pass (hashedPwd, salt) =
             hashPassword password salt == hashedPwd
       case userList of
         [usr] -> if pass usr then return ()
                  else CL.throwIO $ MULLError.NotLoggedIn user
         _     -> CL.throwIO $ MULLError.NoUserFound user


-- | Encodes a @password@ using PBKDF2 (using @salt@ as
-- cryptographic salt, doing 1e4 iterations and creating 1KiB
-- output). It then SHA 512 encodes this.
hashPassword :: Text -> ByteString -> ByteString
hashPassword password salt = CryptoK.fastPBKDF2_SHA512 p t salt
  where p = CryptoK.Parameters 10000 1024
        t = Enc.encodeUtf8 password


-- | Returns a SHA512 hash of 512 bytes of random data 
createSalt :: IO ByteString
createSalt = fst . CryptoR.randomBytesGenerate 512 <$> CryptoR.getSystemDRG


--------------------------------------------------------------------------------
-- Database operations: sessions

-- | Throws @SessionTimeout@ if the session has timed out.
verifySession :: Token -> MULLE v ()
verifySession token = wrapConnection $ \conn -> 
  do sessions <- getLastActive conn token
     -- Compute the difference in time stamps
     newTimeStamp <- Time.getCurrentTime
     -- Check if a session exists and it is has been active in the last 30 minutes
     when (expired sessions newTimeStamp) $
       do deleteSession conn token
          CL.throwIO MULLError.SessionTimeout


-- | Creates a new session and returns the session token.
startSession :: SQL.Connection -> Text -> IO Token
startSession conn user 
  = do -- Remove any existing session.
       SQL.executeNamed conn
         "DELETE FROM Session WHERE User = :User"
         [":User" := user]
       -- Create new session.
       timeStamp <- Time.getCurrentTime
       let token = genToken timeStamp
       SQL.executeNamed conn
         " INSERT INTO Session (User, Token, Starttime, LastActive) \
         \ VALUES (:User, :Token, :Starttime, :LastActive) "
         [ ":User"        := user
         , ":Token"       := token
         , ":Starttime"   := timeStamp
         , ":LastActive"  := timeStamp
         ]
       return token


deleteSession :: SQL.Connection -> Token -> IO ()
deleteSession conn token
  = SQL.executeNamed conn
    "DELETE FROM Session WHERE Token = :Token"
    [ ":Token" := token ]


data SessionToken a = SessionToken Token Text a

instance FromJSON a => FromJSON (SessionToken a) where
  parseJSON = Aeson.withObject "SessionToken" $ \v -> 
    do token <- v .: "token"
       course <- v .: "course"
       value <- parseJSON (Aeson.Object v)
       return (SessionToken token course value)

instance ToJSON a => ToJSON (SessionToken a) where
  toJSON (SessionToken token course value) 
    = Aeson.object ["token" .= token, "course" .= course] `merge` toJSON value
    where Aeson.Object o1 `merge` Aeson.Object o2 = Aeson.Object (o1 <> o2)
          _ `merge` _ = error "merge: incompatible JSON values"

-- mergeValues :: Aeson.Value -> Aeson.Value -> Aeson.Value
-- mergeValues (Aeson.Object o1) (Aeson.Object o2) = Aeson.Object (o1 <> o2)
-- mergeValues (Aeson.Array a1) (Aeson.Array a2) = Aeson.Array (a1 <> a2)
-- mergeValues v1 (Aeson.Array a2) | null a2 = v1
-- mergeValues (Aeson.Array a1) v2 | null a1 = v2
-- mergeValues v1 Aeson.Null = v1
-- mergeValues Aeson.Null v2 = v2
-- mergeValues _ _ = error "mergeValues: incompatible JSON values"


newtype SessionTokenOnly = SessionTokenOnly Token

instance FromJSON SessionTokenOnly where
  parseJSON = Aeson.withObject "SessionTokenOnly" $ \v -> SessionTokenOnly
    <$> v .: "token"

instance ToJSON SessionTokenOnly where
  toJSON (SessionTokenOnly token) = Aeson.object
    [ "token" .= token ]


newtype Token = Token Text
  deriving (ToField, FromField)

instance FromJSON Token where
  parseJSON = Aeson.withText "Token" $ \s -> return (Token s)

instance ToJSON Token where
  toJSON (Token token) = Aeson.String token


-- FIXME Reduce the three-layered string conversion going on here.
genToken :: UTCTime -> Token
genToken = Token . Text.pack . show . hash
           . ByteString.pack . Time.formatTime Time.defaultTimeLocale "%s"
 where hash :: ByteString -> CryptoH.Digest CryptoH.SHA3_512
       hash = CryptoH.hash


-- Check if the token has expired.
expired :: UTCTime -> UTCTime -> Bool
expired oldTimeStamp newTimeStamp = diff > sessionLifeTime
  where diff = newTimeStamp `Time.diffUTCTime` oldTimeStamp


-- TODO Make this configurable.
sessionLifeTime :: NominalDiffTime
sessionLifeTime = 30 * hours
  where hours = 60 * 60 -- seconds

-- Get the last time this token was active
getLastActive :: SQL.Connection -> Token -> IO UTCTime
getLastActive conn token 
  = do xs <- SQL.queryNamed conn
             "SELECT LastActive FROM Session WHERE Token = :Token"
             [":Token" := token]
       case xs of
         [SQL.Only x] -> return x
         _ -> CL.throwIO MULLError.NoCurrentSession
