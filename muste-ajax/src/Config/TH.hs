{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE
    OverloadedStrings
  , DeriveLift
  , RecordWildCards
  , DuplicateRecordFields
  , TemplateHaskell
#-}
module Config.TH (Config(..), config, AppConfig(..), User(..)) where

import Prelude ()
import Muste.Prelude
import System.FilePath
import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Lift(lift))
import Data.Yaml
  ( FromJSON(parseJSON), withObject
  , ToJSON(toJSON), object
  , (.:), (.:?), (.!=), (.=)
  )
import Paths_muste_ajax
import Data.FileEmbed
import Common (decodeFileThrow)

data User = User
  { name     ∷ String
  , password ∷ String
  , enabled  ∷ Bool
  } deriving (Show, Lift)

instance FromJSON User where
  parseJSON = withObject "user" $ \v → User
    <$> v .: "name"
    <*> v .: "password"
    <*> v .: "enabled"

data Config = Config
  { port          ∷ Int
  , wwwRoot       ∷ FilePath
  , staticDir     ∷ FilePath
  , virtualRoot   ∷ FilePath
  , dataDir       ∷ FilePath
  , logDir        ∷ FilePath
  , users         ∷ [User]
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
  parseJSON = withObject "config" $ \v → Config
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

data AppConfig = AppConfig
  { db          ∷ FilePath
  -- A path to the yaml file containing the lessons
  , lessons     ∷ FilePath
  , accessLog   ∷ FilePath
  , errorLog    ∷ FilePath
  , port        ∷ Int
  , staticDir   ∷ FilePath
  , wwwRoot     ∷ FilePath
  , virtualRoot ∷ FilePath
  , users       ∷ [User]
  }

instance ToJSON AppConfig where
  toJSON AppConfig{..} = object
    [ "db"           .= db
    , "lessons"      .= lessons
    , "access-log"   .= accessLog
    , "error-log"    .= errorLog
    , "port"         .= port
    , "static-dir"   .= staticDir
    , "www-root"     .= wwwRoot
    , "virtual-root" .= virtualRoot
    ]
