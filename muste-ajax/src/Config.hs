module Config
  ( getGrammar
  , getDB
  , getStaticDir
  , loggingEnabled
  , webPrefix
  , port
  ) where

import System.FilePath

import qualified Paths_muste_ajax as Paths

staticDir :: FilePath
staticDir = "./static/"

getStaticDir :: IO FilePath
getStaticDir = Paths.getDataFileName staticDir

-- FIXME Use haskell resource files for this.
dataDir :: FilePath
dataDir = "./data/"

grammarDir :: FilePath
grammarDir = dataDir </> "gf/compiled/novo_modo/"

getGrammar :: String -> IO FilePath
getGrammar f = Paths.getDataFileName $ grammarDir </> f <.> "pgf"

getDB :: IO FilePath
getDB = Paths.getDataFileName $ dataDir </> "muste.db"

-- FIXME Handle this with CPP
-- | Switch loggin on/off
loggingEnabled :: Bool
loggingEnabled = True

webPrefix :: FilePath
webPrefix = "/"

port :: Int
port = 8080
