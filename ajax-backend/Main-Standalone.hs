module Main where
import Network.Shed.Httpd
import Network.URI
import Data.List
import System.IO
import Ajax
import Muste
import Muste.Grammar
import PGF
import qualified Data.Map.Strict as Map
import qualified Data.ByteString.Char8 as B
import System.Environment
import Data.IORef
import Data.Maybe
import Data.Map
import Muste.Tree

filePath = "./demo"

getFileName :: String -> String
getFileName "/" = "index.html"
getFileName ('/':fn) = fn

getType :: String -> String
getType fn
  | isSuffixOf "html" fn = "text/html"
  | isSuffixOf "css" fn = "text/css"
  | isSuffixOf "js" fn = "application/javascript"
  | isSuffixOf "ico" fn = "image/x-icon"
  | otherwise = "text/plain"


handleRequest :: Grammar -> IORef (Maybe Precomputed) -> Bool -> Request -> IO Response
handleRequest grammar prec isDemo request
  -- | isPrefixOf "/cgi"(uriPath $ reqURI request) =
  --     do
  --       putStrLn $ "CGI" ++ (show request)
  --       prec <- initPrecomputed grammar prec (reqBody request)
  --       result <- if isDemo then handleClientRequest grammar demoPrec (reqBody request)
  --                 else handleClientRequest grammar prec (reqBody request)
  --       return (Response 200 [("Content-type","application/json")] result)

  | otherwise = 
      do
        putStrLn $ "HTTP" ++ (show request)
        let file = getFileName $ uriPath $ reqURI request
        let typ = getType file
        content <- B.readFile $ filePath ++ "/" ++ file
        return (Response 200 [("Content-type",typ)] $ B.unpack content)

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
      else do { server <- initServer 8080 (handleRequest dbConn grammars precs) ; return () }
