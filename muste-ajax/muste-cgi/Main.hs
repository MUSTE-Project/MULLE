module Main where

import Network.CGI
import Control.Monad
import qualified Protocol

-- FIXME Do not depend on `PGF` - may need to export functionality
-- from `muste`.
import qualified PGF (readPGF)

import Muste

import Ajax

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
    pgf <- PGF.readPGF "Grammar.pgf"
    let grammar = pgfToGrammar pgf
    runCGI (cgi grammar)
