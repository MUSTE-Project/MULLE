{-# LANGUAGE
    CPP
  , UnicodeSyntax
  , NamedWildCards
  , OverloadedStrings
  , DeriveLift
  , RecordWildCards
  , DuplicateRecordFields
  , TemplateHaskell
#-}
module Config.TH (Config(..), config, AppConfig(..)) where

import System.FilePath
import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Lift(lift))
import Control.Exception (throwIO)
import Control.Monad
import Control.Monad.IO.Class (MonadIO(liftIO))
import Data.ByteString (ByteString)
import Data.Yaml
  ( FromJSON(parseJSON), withObject
  , ToJSON(toJSON), object
  , (.:), (.:?), (.!=), (.=)
  )
#if MIN_VERSION_yaml(0,8,31)
import qualified Data.Yaml as Yaml (decodeFileThrow)
#else
import qualified Data.Yaml as Yaml (decodeFileEither)
#endif
import Paths_muste_ajax

data Config = Config
  { port          ∷ Int
  , wwwRoot       ∷ FilePath
  , staticDir     ∷ FilePath
  , virtualRoot   ∷ FilePath
  , serveRelative ∷ Bool
  , dataDir       ∷ FilePath
  , logDir        ∷ FilePath
  } deriving (Lift)

shareDir ∷ FilePath
shareDir = $( runIO getDataDir >>= lift )

defaultPort ∷ Int
defaultPort = 80

defaultWwwRoot ∷ FilePath
defaultWwwRoot = shareDir </> "www"

defaultStaticDir ∷ FilePath
defaultStaticDir = "static"

defaultVirtualRoot ∷ FilePath
defaultVirtualRoot = mempty

defaultServeStaticRelative ∷ Bool
defaultServeStaticRelative = False

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
    <*> v .:? "serve-static-relative" .!= defaultServeStaticRelative
    <*> v .:? "data-dir"              .!= defaultDataDir
    <*> v .:? "log-dir"               .!= defaultLogDir

decodeFileThrow ∷ MonadIO m ⇒ FromJSON a ⇒ FilePath → m a
#if MIN_VERSION_yaml(0,8,31)
decodeFileThrow = Yaml.decodeFileThrow
#else
decodeFileThrow f = liftIO $ Yaml.decodeFileEither f >>= either throwIO return
#endif

decodeConfig ∷ IO Config
decodeConfig = decodeFileThrow "config.yaml"

config ∷ Q Exp
config = runIO decodeConfig >>= lift

data AppConfig = AppConfig
  { db          ∷ FilePath
  , accessLog   ∷ FilePath
  , errorLog    ∷ FilePath
  , port        ∷ Int
  , staticDir   ∷ FilePath
  , wwwRoot     ∷ FilePath
  , virtualRoot ∷ FilePath
  }

instance ToJSON AppConfig where
  toJSON (AppConfig { .. }) = object
    [ "db"          .= db
    , "accessLog"   .= accessLog
    , "errorLog"    .= errorLog
    , "port"        .= port
    , "staticDir"   .= staticDir
    , "wwwRoot"     .= wwwRoot
    , "virtualRoot" .= virtualRoot
    ]
