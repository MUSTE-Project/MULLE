-- | Transforms the configuration file into the app config.
--
-- Module      : Muste.Web.Config.AppConfig
-- License     : Artistic License 2.0
-- Stability   : experimental
-- Portability : POSIX

{-# Language RecordWildCards, OverloadedStrings #-}
{-# OPTIONS_GHC -Wall -Wcompat #-}

module Muste.Web.Config.AppConfig
  ( AppConfig(..)
  ) where

import Data.Aeson (ToJSON(..), (.=))
import qualified Data.Aeson as Aeson

import qualified Muste.Web.Config.Types as Types

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

instance ToJSON AppConfig where
  toJSON AppConfig{..} = Aeson.object
    [ "db"           .= db
    , "lessons"      .= lessons
    , "access-log"   .= accessLog
    , "error-log"    .= errorLog
    , "port"         .= port
    , "static-dir"   .= staticDir
    , "virtual-root" .= virtualRoot
    ]
