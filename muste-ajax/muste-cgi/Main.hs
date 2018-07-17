module Main where

import Network.CGI

-- FIXME Do not depend on `PGF` - may need to export functionality
-- from `muste`.
import qualified PGF (readPGF)

import Muste

-- TODO Now that we no longer have @Protocol.handleClientRequest@ we
-- should make this a sub componennf of the main snap (in the
-- @muste-ajax@ component).
cgi :: Grammar -> CGI CGIResult
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
