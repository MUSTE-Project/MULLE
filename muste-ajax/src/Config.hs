module Config
  ( getGrammar
  , getDB
  , loggingEnabled
  , logFile
  , demoDir
  , webPrefix
  , port
  ) where

import System.FilePath

import qualified Paths_muste_ajax as Paths

-- FIXME Use haskell resource files for this.
dataDir :: FilePath
dataDir = "data/"

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

logFile :: FilePath
logFile = "messagelog.txt"

-- FIXME Use haskell resource files for this.
demoDir :: FilePath
demoDir = "./demo"

webPrefix :: FilePath
webPrefix = "/"

port :: Int
port = 8080
