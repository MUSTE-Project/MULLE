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

getFileContent =
  readFile 
handleRequest :: Grammar -> Request -> IO Response
handleRequest grammar request
  | isPrefixOf "/cgi"(uriPath $ reqURI request) =
      do
        putStrLn $ "CGI" ++ (show request)
        let cm = decodeClientMessage (reqBody request)
        -- Get new Success
        let nscore = cscore cm + 1
        -- Check for Success
        let ctreea = ctree $ ca cm
        let ctreeb = ctree $ cb cm
        let nsuccess = ctreea == ctreeb
        -- Get new Suggestions
        let langa = (cgrammar $ ca cm)
        let langb = (cgrammar $ cb cm)
        let na = ST {
              sgrammar = langa, -- same language again
              stree = ctreea,
              slin = (linearizeTree grammar langa ctreea), -- linearization
              smenu = (generateMenus (grammar, mkCId langa) ctreea) -- menus
              }
        let nb = ST {
              sgrammar = langb, -- same language again
              stree = ctreeb,
              slin = (linearizeTree grammar langb ctreeb), -- linearization linearizeTree ctreeb
              smenu = (generateMenus (grammar, mkCId langb) ctreeb) -- menus
              }
        -- New ServerMessage
        let nsm = (SM nsuccess nscore na nb)
        putStrLn $ "\n\n" ++ (show nsm) ++ "#"
        return (Response 200 [("Content-type","application/json")] (encodeServerMessage nsm))

  | otherwise = 
      do
        putStrLn $ "HTTP" ++ (show request)
        let file = getFileName $ uriPath $ reqURI request
        let typ = getType file
        content <- getFileContent $ filePath ++ "/" ++ file
        return (Response 200 [("Content-type",typ)] content)
                
main :: IO ()
main =
  do
    pgf <- readPGF "Grammar.pgf"
    let grammar = pgfToGrammar pgf
    server <-initServer 8080 (handleRequest grammar)
    putStrLn "Server exited"
