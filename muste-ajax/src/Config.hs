module Config (getGrammar, getDB) where

import System.FilePath

import qualified Paths_muste_ajax as Paths

dataDir :: FilePath
dataDir = "data/"

grammarDir :: FilePath
grammarDir = dataDir </> "gf/compiled/novo_modo/"

getGrammar :: String -> IO FilePath
getGrammar f = Paths.getDataFileName $ grammarDir </> f <.> "pgf"

getDB :: IO FilePath
getDB = Paths.getDataFileName $ dataDir </> "muste.db"

