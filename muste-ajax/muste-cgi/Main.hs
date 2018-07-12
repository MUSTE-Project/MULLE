module Main where

import Network.CGI
import Control.Monad
import Ajax
import Muste
import Muste.Grammar
import PGF
import qualified Protocol

cgi:: Grammar -> CGI CGIResult
cgi grammar =
  do
    setHeader "Content-type" "text/json"
    b <- getBody
    liftIO $ putStrLn $ "CGI" ++ b
    result <- error "Main.cgi: Not yet implemented"
    output result
    
main :: IO ()
main =
  do
    pgf <- readPGF "Grammar.pgf"
    let grammar = pgfToGrammar pgf
    runCGI (cgi grammar)
