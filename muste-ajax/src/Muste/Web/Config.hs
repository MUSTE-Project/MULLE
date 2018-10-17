-- | Exposes configuration options to the rest of the application.--
--
-- Module      : Muste.Web.Config
-- License     : Artistic License 2.0
-- Stability   : experimental
-- Portability : POSIX
--
-- The configuration options that are exposed to the rest of this
-- application.

-- FIXME Name shadowing.
{-# OPTIONS_GHC -Wall -Wcompat -Wno-name-shadowing #-}
{-# LANGUAGE
    UnicodeSyntax
  , NamedWildCards
  , TemplateHaskell
  , RecordWildCards
  , DuplicateRecordFields
#-}

module Muste.Web.Config
  ( AppConfig
  , appConfig
  , db
  , lessons
  , accessLog
  , errorLog
  , port
  , staticDir
  , wwwRoot
  , virtualRoot
  , users
  , Types.User(..)
  ) where

import System.FilePath ((</>), (<.>))

import           Muste.Web.Config.AppConfig (AppConfig(AppConfig))
import qualified Muste.Web.Config.AppConfig as AppConfig
import qualified Muste.Web.Config.TH    as Cfg
import qualified Muste.Web.Config.Types as Types

cfg ∷ Cfg.Config
cfg = $( Cfg.config )

appConfig ∷ AppConfig
appConfig = fromConfig cfg

fromConfig ∷ Cfg.Config → AppConfig
fromConfig Cfg.Config{..} = AppConfig
  { db          = dataDir </> "muste"     <.> "sqlite3"
  , lessons     = dataDir </> "lessons"   <.> "yaml"
  , accessLog   = logDir  </> "access"    <.> "log"
  , errorLog    = logDir  </> "error"     <.> "log"
  , port        = port
  , staticDir   = staticDir
  , wwwRoot     = wwwRoot
  , virtualRoot = virtualRoot
  , users       = users
  }
  where
  logDir  = Cfg.logDir cfg
  dataDir = Cfg.dataDir cfg

staticDir     ∷ FilePath
staticDir     = AppConfig.staticDir appConfig

port          ∷ Int
port          = AppConfig.port appConfig

wwwRoot       ∷ FilePath
wwwRoot       = AppConfig.wwwRoot appConfig

virtualRoot   ∷ FilePath
virtualRoot   = AppConfig.virtualRoot appConfig

db            ∷ FilePath
db            = AppConfig.db appConfig

lessons       ∷ FilePath
lessons       = AppConfig.lessons appConfig

accessLog     ∷ FilePath
accessLog     = AppConfig.accessLog appConfig

errorLog      ∷ FilePath
errorLog      = AppConfig.errorLog appConfig

users         ∷ [Types.User]
users         = AppConfig.users appConfig
