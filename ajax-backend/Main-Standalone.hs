module Main.Standalone where
import Network.Shed.Httpd
import Ajax

handleRequest :: Request -> IO Response
handleRequest request =
  do
    let cm = decodeClientMessage (reqBody request)
    return (Response 200 [("Content-type","text/json")] (show (cscore cm + 1))) 
main :: IO ()
main =
  do
    server <-initServer 8080 handleRequest
    putStrLn "Server exited"
