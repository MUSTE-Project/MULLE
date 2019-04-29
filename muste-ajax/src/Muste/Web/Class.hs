{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language
 OverloadedStrings
#-}

module Muste.Web.Class
  ( MULLE
  , AppState(..)
  , wrapConnection
  , MULLError(..)
  , errorResponseCode
  ) where

import Control.Exception (Exception(displayException))
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (asks)

import qualified Snap
import Database.SQLite.Simple (Connection)

import qualified Data.Text as Text
import Data.Text (Text)

import qualified Muste


----------------------------------------------------------------------
-- The MULLE monad

type MULLE v a = Snap.Handler v AppState a

-- | The state that the server will have throughout the uptime.
data AppState = AppState
  { connection    :: Connection
  , lessonsCfg    :: FilePath
  , muState       :: Muste.MUState
  }

wrapConnection :: (Connection -> IO a) -> MULLE v a
wrapConnection action
  = do conn <- asks connection
       liftIO $ action conn


----------------------------------------------------------------------
-- Errors

data MULLError
  = MissingApiRoute String
  | NoAccessToken
  | BadRequest
  | RequestBodyError
  | SessionInvalid
  | NoCurrentSession
  | SessionTimeout
  | LoginFail
  | JSONDecodeError String
  | GrammarNotFound Text
  | LanguageNotFound Text
  | NoUserFound Text
  | NotLoggedIn Text
  | UserAlreadyExists Text
  deriving Show

instance Exception MULLError where
  displayException err = case err of
    MissingApiRoute s   -> "Missing api route: " ++ s
    NoAccessToken       -> "No cookie found"
    BadRequest          -> "Bad request"
    RequestBodyError    -> "Error reading request body"
    SessionInvalid      -> "Session invalid, please log in again"
    NoCurrentSession    -> "No current session"
    SessionTimeout      -> "Session timeout"
    LoginFail           -> "Login failure"
    JSONDecodeError s   -> "Error decoding JSON: " ++ s
    GrammarNotFound g   -> "Grammar not found: " ++ Text.unpack g
    LanguageNotFound l  -> "Language not found: " ++ Text.unpack l
    NoUserFound u       -> "No user found: " ++ Text.unpack u
    NotLoggedIn u       -> "User is not logged in: " ++ Text.unpack u
    UserAlreadyExists u -> "The username is already taken: " ++ Text.unpack u

errorResponseCode :: MULLError -> Int
errorResponseCode err = case err of
  MissingApiRoute{}  -> 501
  NoAccessToken      -> 401
  BadRequest         -> 400
  RequestBodyError   -> 400
  SessionInvalid     -> 400
  NoCurrentSession   -> 401
  SessionTimeout     -> 401
  LoginFail          -> 401
  JSONDecodeError{}  -> 400
  GrammarNotFound{}  -> 400
  LanguageNotFound{} -> 400
  NoUserFound{}      -> 401
  NotLoggedIn{}      -> 401
  UserAlreadyExists{}-> 400

