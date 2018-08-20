{-# LANGUAGE
    UnicodeSyntax
  , NamedWildCards
  , TemplateHaskell
  , RecordWildCards
  , DuplicateRecordFields
#-}
module Config
  ( App.AppConfig
  , appConfig
  , Config.db
  , Config.accessLog
  , Config.errorLog
  , Config.port
  , Config.staticDir
  , Config.wwwRoot
  , Config.virtualRoot
  ) where

import qualified Config.TH as CFG hiding (AppConfig(..))
import Config.TH as App (AppConfig(..))
import System.FilePath ((</>), (<.>))

cfg ∷ CFG.Config
cfg = $( CFG.config )

appConfig ∷ AppConfig
appConfig = fromConfig cfg

fromConfig ∷ CFG.Config → AppConfig
fromConfig (CFG.Config { .. }) = AppConfig
  { db          = dataDir </> "muste"  <.> "sqlite3"
  , accessLog   = logDir  </> "access" <.> "log"
  , errorLog    = logDir  </> "error"  <.> "log"
  , port        = port
  , staticDir   = staticDir
  , wwwRoot     = wwwRoot
  , virtualRoot = virtualRoot
  }
  where
  logDir  = CFG.logDir cfg
  dataDir = CFG.dataDir cfg

staticDir     ∷ FilePath
staticDir     = App.staticDir appConfig

port          ∷ Int
port          = App.port appConfig

wwwRoot       ∷ FilePath
wwwRoot       = App.wwwRoot appConfig

virtualRoot   ∷ FilePath
virtualRoot   = App.virtualRoot appConfig

db            ∷ FilePath
db            = App.db appConfig

accessLog     ∷ FilePath
accessLog     = App.accessLog appConfig

errorLog      ∷ FilePath
errorLog      = App.errorLog appConfig
