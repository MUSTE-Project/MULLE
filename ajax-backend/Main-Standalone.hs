{-# LANGUAGE OverloadedStrings #-}
module Main where
--import Network.Shed.Httpd
import Network.URI
import Network.Wai.Handler.Warp
import Network.Wai
import Network.HTTP.Types.Status

import Data.List
import System.IO
import Ajax
import Muste
import Muste.Grammar
import PGF
import qualified Data.Map.Strict as Map
import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Lazy as LB
import System.Environment
import Data.Maybe
import Data.Map
import Muste.Tree
import Database.SQLite.Simple
import Database hiding (main)
import Protocol
import Data.Time
import Control.Monad

-- Switch loggin on/off
logging = True
logFile = "messagelog.txt"

filePath = "./demo"
webPrefix = "/"
getFileName :: String -> String
-- getFileName "/" = "index.html"
-- getFileName ('/':fn) = fn
getFileName name
  | name == webPrefix = "index.html"
  | isPrefixOf webPrefix name = drop (length webPrefix) name
  | otherwise = error $ "bad name " ++ name
    
getType :: String -> String
getType fn
  | isSuffixOf "html" fn = "text/html"
  | isSuffixOf "css" fn = "text/css"
  | isSuffixOf "js" fn = "application/javascript"
  | isSuffixOf "ico" fn = "image/x-icon"
  | otherwise = "text/plain"

-- Lesson -> Grammar
handleRequest :: Connection -> Map String Grammar -> LessonsPrecomputed -> Application
handleRequest conn grammars prec request response    
  | isInfixOf ("/cgi") (B.unpack $ rawPathInfo request) =
      do
        putStrLn $ "CGI-Request" ++ (show request)        
        body <- fmap (B.unpack . LB.toStrict) $ strictRequestBody request
        when logging (do { timestamp <- formatTime defaultTimeLocale "%s" <$> getCurrentTime ; appendFile logFile $ timestamp ++ "\tCGI-Request\t" ++ show body ++ "\n"})
        result <- handleClientRequest conn grammars prec body
        when logging (do { timestamp <- formatTime defaultTimeLocale "%s" <$> getCurrentTime ; appendFile logFile $ timestamp ++ "\tCGI-Response\t" ++ show result ++ "\n"}) 
        response (responseLBS status200 [("Content-type","application/json")] $ LB.fromStrict $ B.pack result)
  | otherwise = 
      do
        putStrLn $ "HTTP" ++ (show request)
        let file = getFileName $ B.unpack $ rawPathInfo request
        let typ = getType file
        content <- B.readFile $ filePath ++ "/" ++ file
        response (responseLBS status200 [("Content-type",B.pack typ)] $ LB.fromStrict content)
printHelp :: IO ()
printHelp =
  do
    putStrLn "Standalone backend for muste."



main :: IO ()
main =
  do
    args <- getArgs
    dbConn <- open "muste.db"
    (grammars,precs) <- initPrecomputed dbConn
    let isHelp = elem "--help" args
    if isHelp then printHelp
    else runSettings (setPort 8080 defaultSettings) (handleRequest dbConn grammars precs)
