module Main.CGI where

import Network.CGI
import Control.Monad
import Ajax

cgi:: CGI CGIResult
cgi =
  do
    setHeader "Content-type" "text/json"
    b <- getBody
    outputNothing
    
main :: IO ()
main =
  runCGI cgi
