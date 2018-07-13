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
import Protocol
import Data.Time
import Control.Monad

import Muste

import qualified Config

getFileName :: String -> String
getFileName name
  | name == Config.webPrefix = "index.html"
  | isPrefixOf Config.webPrefix name = Prelude.drop (length Config.webPrefix) name
  | otherwise = error $ "bad name " ++ name

getType :: String -> String
getType fn
  | isSuffixOf "html" fn = "text/html"
  | isSuffixOf "css" fn = "text/css"
  | isSuffixOf "js" fn = "application/javascript"
  | isSuffixOf "ico" fn = "image/x-icon"
  | otherwise = "text/plain"

-- Lesson -> (Language -> Context)
handleRequest :: Connection -> Map String (Map String Context) -> Application
handleRequest conn contexts request response
  | isInfixOf ("/cgi") (B.unpack $ rawPathInfo request) =
      do
        putStrLn $ "CGI-Request" ++ (show request)
        body <- fmap (B.unpack . LB.toStrict) $ strictRequestBody request
        when Config.loggingEnabled (do { timestamp <- formatTime defaultTimeLocale "%s" <$> getCurrentTime ; appendFile Config.logFile $ timestamp ++ "\tCGI-Request\t" ++ show body ++ "\n"})
        result <- handleClientRequest conn contexts body
        when Config.loggingEnabled (do { timestamp <- formatTime defaultTimeLocale "%s" <$> getCurrentTime ; appendFile Config.logFile $ timestamp ++ "\tCGI-Response\t" ++ show result ++ "\n"})
        response (responseLBS status200 [("Content-type","application/json")] $ result)
  | otherwise =
      do
        putStrLn $ "HTTP" ++ (show request)
        let file = getFileName $ B.unpack $ rawPathInfo request
        let typ = getType file
        content <- B.readFile $ Config.demoDir ++ "/" ++ file
        response (responseLBS status200 [("Content-type",B.pack typ)] $ LB.fromStrict content)

printHelp :: IO ()
printHelp =
  do
    putStrLn "Standalone backend for muste."

main :: IO ()
main =
  do
    args <- getArgs
    dbConn <- Config.getDB >>= open
    contexts <- initContexts dbConn
    let isHelp = elem "--help" args
    if isHelp then printHelp
      else do
      putStrLn "Running server on port 8080"
      runSettings (setPort 8080 defaultSettings) (handleRequest dbConn contexts)
