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
  ( AppConfig(..)
  , appConfig
  , Types.User(..)
  ) where

import Prelude ()
import Muste.Prelude
import Muste.Prelude.Extra (decodeFileThrow)

import System.FilePath (takeDirectory, (</>), (<.>))
import Data.Aeson (FromJSON(..), ToJSON(..), (.:?), (.!=), (.=))
import qualified Data.Aeson as Aeson

import qualified Muste.Web.Config.Types as Types

appConfig ∷ FilePath -> IO AppConfig
appConfig cfgFile =
  do cfg@AppConfig{..} <- decodeFileThrow cfgFile
     return cfg { db = cfgDir </> db
                , lessons = cfgDir </> lessons
                , accessLog = cfgDir </> accessLog
                , errorLog = cfgDir </> errorLog
                , staticDir = cfgDir </> staticDir
                }
  where cfgDir = takeDirectory cfgFile

defaultDB :: FilePath
defaultDB = defaultDataDir </> "muste" <.> "sqlite3"

defaultLessons :: FilePath
defaultLessons = "lessons" <.> "yaml"

defaultAccessLog :: FilePath
defaultAccessLog = defaultLogDir  </> "access" <.> "log"

defaultErrorLog :: FilePath
defaultErrorLog = defaultLogDir  </> "error" <.> "log"

defaultPort ∷ Int
defaultPort = 8080

defaultStaticDir ∷ FilePath
defaultStaticDir = "static"

defaultVirtualRoot ∷ FilePath
defaultVirtualRoot = mempty

defaultDataDir ∷ FilePath
defaultDataDir = "data"

defaultLogDir ∷ FilePath
defaultLogDir = "log"


data AppConfig = AppConfig
  { db          ∷ FilePath
  -- A path to the yaml file containing the lessons
  , lessons     ∷ FilePath
  , accessLog   ∷ FilePath
  , errorLog    ∷ FilePath
  , port        ∷ Int
  , staticDir   ∷ FilePath
  , virtualRoot ∷ FilePath
  , users       ∷ [Types.User]
  }

instance FromJSON AppConfig where
  parseJSON = Aeson.withObject "app-config" $ \v → AppConfig
    <$> v .:? "db"                    .!= defaultDB
    <*> v .:? "lessons"               .!= defaultLessons
    <*> v .:? "access-log"            .!= defaultAccessLog
    <*> v .:? "error-log"             .!= defaultErrorLog
    <*> v .:? "port"                  .!= defaultPort
    <*> v .:? "static-dir"            .!= defaultStaticDir
    <*> v .:? "virtual-root"          .!= defaultVirtualRoot
    <*> v .:? "users"                 .!= mempty

instance ToJSON AppConfig where
  toJSON AppConfig{..} = Aeson.object
    [ "db"           .= db
    , "lessons"      .= lessons
    , "access-log"   .= accessLog
    , "error-log"    .= errorLog
    , "port"         .= port
    , "static-dir"   .= staticDir
    , "virtual-root" .= virtualRoot
    , "users"        .= users
    ]
