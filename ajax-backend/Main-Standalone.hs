module Main where
import Network.Shed.Httpd
import Network.URI
import Data.List
import System.IO
import Ajax

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
handleRequest :: Request -> IO Response
handleRequest request
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
        let na = ST (cgrammar $ ca cm) -- same language again
                    (linearizeTree ctreea) -- linearization
                    (generateMenus ctreea) -- menus
        let nb = ST (cgrammar $ cb cm) -- same language again
                    (linearizeTree ctreeb) -- linearization
                    (generateMenus ctreeb) -- menus
        -- New ServerMessage
        let nsm = (SM nsuccess nscore na nb)
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
    server <-initServer 8080 handleRequest
    putStrLn "Server exited"
