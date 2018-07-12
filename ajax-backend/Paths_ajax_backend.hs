-- | Beware this module does magic!
--
-- See e.g. http://neilmitchell.blogspot.com/2008/02/adding-data-files-using-cabal.html
-- for more information.
module Paths_ajax_backend (getGrammar, getDB) where

import System.FilePath

dataDir :: FilePath
dataDir = "data/"

grammarDir :: FilePath
grammarDir = dataDir </> "gf/compiled/novo_modo/"

getGrammar :: String -> IO FilePath
getGrammar f = getDataFileName $ grammarDir </> f <.> "pgf"

getDB :: IO FilePath
getDB = getDataFileName $ dataDir </> "muste.db"

getDataFileName :: FilePath -> IO FilePath
getDataFileName = pure
