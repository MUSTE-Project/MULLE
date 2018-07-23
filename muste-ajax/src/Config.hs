{-# LANGUAGE CPP #-}
module Config
  ( getGrammar
  , getDB
  , getStaticDir
  , getErrorLog
  , getAccessLog
  , loggingEnabled
  , webPrefix
  , port
  ) where

import System.FilePath

import qualified Paths_muste_ajax as Paths

staticDir :: FilePath
staticDir = "./static/"

getStaticDir :: IO FilePath
#ifdef RELATIVE_PATHS
getStaticDir = pure staticDir
#else
getStaticDir = Paths.getDataFileName staticDir
#endif

-- FIXME Use haskell resource files for this.
dataDir :: FilePath
dataDir = "./data/"

grammarDir :: FilePath
grammarDir = dataDir </> "gf/compiled/novo_modo/"

getGrammar :: String -> IO FilePath
getGrammar f = Paths.getDataFileName $ grammarDir </> f <.> "pgf"

getDB :: IO FilePath
getDB = Paths.getDataFileName $ dataDir </> "muste.db"

-- FIXME Should we maybe log to the current dir (rather than the
-- shared resource returned by Haskells data-files construct) or to
-- /var/log/?
logDir :: FilePath
logDir = "./log/"

getLogDir :: IO FilePath
getLogDir = Paths.getDataFileName logDir

getAccessLog :: IO FilePath
getAccessLog = (</> "access.log") <$> getLogDir

getErrorLog :: IO FilePath
getErrorLog = (</> "error.log") <$> getLogDir

-- FIXME Handle this with CPP
-- | Switch loggin on/off
loggingEnabled :: Bool
loggingEnabled = True

webPrefix :: FilePath
webPrefix = "/"

port :: Int
port = 8080
