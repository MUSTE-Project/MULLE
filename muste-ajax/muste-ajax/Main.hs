{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Network.Wai.Handler.Warp
import Network.Wai
import Network.HTTP.Types.Status
import Data.List
import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Lazy as LB
import System.Environment
import Data.Map
import Database.SQLite.Simple
import Database hiding (main)
import Data.Time
import Control.Monad
import Text.Printf
import System.FilePath

import Muste

import qualified Protocol
import qualified Config

getFileName :: String -> String
getFileName name
  | name == Config.webPrefix = "index.html"
  | isPrefixOf Config.webPrefix name = Prelude.drop (length Config.webPrefix) name
  | otherwise = printf "bad name %s" name

-- | Determine mime type based on file name.
getType :: String -> String
getType fn
  | "html" `isSuffixOf` fn = "text/html"
  | "css"  `isSuffixOf` fn = "text/css"
  | "js"   `isSuffixOf` fn = "application/javascript"
  | "ico"  `isSuffixOf` fn = "image/x-icon"
  | otherwise              = "text/plain"

-- TODO Logging is currently too lazy. This is my fault because I
-- changed from packing and unpacking lazy bytestreams to directly
-- outputting lazy streams with 'printf' a few commits ago.
-- | Handles both HTTP requests and API requests.
--
-- HTTP requests serve up files in @Config.demoDir@.  API requests are
-- handled according to @Protocol.handleClientRequest@.
handleRequest :: Connection -> Map String (Map String Context) -> Application
handleRequest conn contexts request response
  | "/cgi" `B.isInfixOf` rawPathInfo request = handleCgi
  | otherwise = handleHttp
  where
  handleCgi :: IO ResponseReceived
  handleCgi = do
    printf "CGI-Request %s\n" (show request)
    body <- strictRequestBody request
    when Config.loggingEnabled $ logTimestamp (show body)
    result <- Protocol.handleClientRequest conn contexts body
    when Config.loggingEnabled $ logTimestamp (show result)
    response
      $ responseLBS status200 [("Content-type","application/json")]
      $ result
  handleHttp :: IO ResponseReceived
  handleHttp = do
    printf "HTTP %s\n" (show request)
    let file = getFileName $ B.unpack $ rawPathInfo request
    let typ = getType file
    content <- LB.readFile $ Config.demoDir </> file
    response
      $ responseLBS status200 [("Content-type",B.pack typ)]
      $ content
  logTimestamp :: String -> IO ()
  logTimestamp s = do
      timestamp <- formatTime defaultTimeLocale "%s" <$> getCurrentTime
      appendFile Config.logFile
        $ printf "%s\tCGI-Response\t%s\n" timestamp s

main :: IO ()
main = do
  args <- getArgs
  dbConn <- Config.getDB >>= open
  contexts <- initContexts dbConn
  putStrLn $ "Running server on port " <> show Config.port
  runSettings
    (setPort Config.port defaultSettings)
    (handleRequest dbConn contexts)
