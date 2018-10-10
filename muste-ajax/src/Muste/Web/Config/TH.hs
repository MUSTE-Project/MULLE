-- | This module described the configuration options as they are read
-- from the config file.  Further processing is then performed on
-- these options.  See the module "Muste.Web.Config.AppConfig" for
-- more information about that.
{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE
    OverloadedStrings
  , DeriveLift
  , RecordWildCards
  , DuplicateRecordFields
  , TemplateHaskell
#-}
module Muste.Web.Config.TH
  ( Config(..), config) where

import Prelude ()
import Muste.Prelude
import Muste.Prelude.Extra

import System.FilePath
import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Lift(lift))
import Data.Aeson (FromJSON(..), (.:?), (.!=))
import qualified Data.Aeson as Aeson

import Paths_muste_ajax
import Data.FileEmbed

import qualified Muste.Web.Config.Types as Types

data Config = Config
  { port          ∷ Int
  , wwwRoot       ∷ FilePath
  , staticDir     ∷ FilePath
  , virtualRoot   ∷ FilePath
  , dataDir       ∷ FilePath
  , logDir        ∷ FilePath
  , users         ∷ [Types.User]
  } deriving (Lift)

shareDir ∷ FilePath
shareDir = $( runIO getDataDir >>= lift )

defaultPort ∷ Int
defaultPort = 80

defaultWwwRoot ∷ FilePath
defaultWwwRoot = shareDir </> "www"

defaultStaticDir ∷ FilePath
defaultStaticDir = shareDir </> "static"

defaultVirtualRoot ∷ FilePath
defaultVirtualRoot = mempty

defaultDataDir ∷ FilePath
defaultDataDir = shareDir </> "data"

defaultLogDir ∷ FilePath
defaultLogDir = shareDir </> "log"

instance FromJSON Config where
  parseJSON = Aeson.withObject "config" $ \v → Config
    <$> v .:? "port"                  .!= defaultPort
    <*> v .:? "www-root"              .!= defaultWwwRoot
    <*> v .:? "static-dir"            .!= defaultStaticDir
    <*> v .:? "virtual-root"          .!= defaultVirtualRoot
    <*> v .:? "data-dir"              .!= defaultDataDir
    <*> v .:? "log-dir"               .!= defaultLogDir
    <*> v .:? "users"                 .!= mempty

decodeConfig ∷ Q Exp
decodeConfig = do
  p ← makeRelativeToProject "config.yaml"
  cfg ← runIO $ decodeFileThrow @_ @Config p
  lift cfg

config ∷ Q Exp
config = decodeConfig
