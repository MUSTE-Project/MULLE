module Main where
import Network.Shed.Httpd
import Network.URI
import Data.List
import System.IO
import Ajax
--import Muste
import Muste.Grammar
import PGF
import qualified Data.Map.Strict as Map

filePath = "./demo"

getFileName :: String -> String
getFileName "/" = "muste.html"
getFileName ('/':fn) = fn

getType :: String -> String
getType fn
  | isSuffixOf "html" fn = "text/html"
  | isSuffixOf "css" fn = "text/css"
  | isSuffixOf "js" fn = "application/javascript"
  | otherwise = "text/plain"

handleRequest :: Grammar -> Request -> IO Response
handleRequest grammar request
  | isPrefixOf "/cgi"(uriPath $ reqURI request) =
      do
        putStrLn $ "CGI" ++ (show request)
        result <- handleClientRequest grammar (reqBody request)
        return (Response 200 [("Content-type","application/json")] result)

  | otherwise = 
      do
        putStrLn $ "HTTP" ++ (show request)
        let file = getFileName $ uriPath $ reqURI request
        let typ = getType file
        content <- readFile $ filePath ++ "/" ++ file
        return (Response 200 [("Content-type",typ)] content)
                
main :: IO ()
main =
  do
    pgf <- readPGF "Grammar.pgf"
    let grammar = pgfToGrammar pgf
    server <-initServer 8080 (handleRequest grammar)
    putStrLn "Server exited"
