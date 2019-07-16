{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language
 DuplicateRecordFields,
 OverloadedStrings
#-}

module Muste.Web.Config
  ( appConfig
  , AppConfig(..)
  , Course(..)
  , Grammar(..)
  , GrammarOptions(..)
  , InitialUser(..)
  ) where

import System.FilePath (takeDirectory, (</>), (<.>))
import Data.Aeson (FromJSON(..), ToJSON(..), (.:), (.:?), (.!=), (.=))
import qualified Data.Aeson as Aeson
import qualified Data.Yaml as Yaml
import Data.Text (Text)


appConfig :: FilePath -> IO AppConfig
appConfig cfgFile =
  do cfg <- Yaml.decodeFileThrow cfgFile
     return $
       if not (null (cfgDir cfg)) then cfg
       else cfg { cfgDir = takeDirectory cfgFile }


defaultDB :: FilePath
defaultDB = defaultDataDir </> "muste" <.> "sqlite3"

defaultAccessLog :: FilePath
defaultAccessLog = defaultDataDir  </> "access" <.> "log"

defaultErrorLog :: FilePath
defaultErrorLog = defaultDataDir  </> "error" <.> "log"

defaultPort :: Int
defaultPort = 8080

defaultStaticDir :: FilePath
defaultStaticDir = "static"

defaultVirtualRoot :: FilePath
defaultVirtualRoot = mempty

defaultDataDir :: FilePath
defaultDataDir = "data"


data AppConfig = AppConfig
  { cfgDir      :: FilePath  -- the location of this config file
  , grammars    :: [Grammar]
  , coursesCfgs :: [Course]
  , db          :: FilePath
  , accessLog   :: FilePath
  , errorLog    :: FilePath
  , port        :: Int
  , staticDir   :: FilePath
  , virtualRoot :: FilePath
  , users       :: [InitialUser]
  }

instance FromJSON AppConfig where
  parseJSON = Aeson.withObject "app-config" $ \v -> AppConfig
    <$> v .:? "cfg-dir"               .!= ""
    <*> v .:  "grammars"
    <*> v .:  "courses"
    <*> v .:? "db"                    .!= defaultDB
    <*> v .:? "access-log"            .!= defaultAccessLog
    <*> v .:? "error-log"             .!= defaultErrorLog
    <*> v .:? "port"                  .!= defaultPort
    <*> v .:? "static-dir"            .!= defaultStaticDir
    <*> v .:? "virtual-root"          .!= defaultVirtualRoot
    <*> v .:? "users"                 .!= []

instance ToJSON AppConfig where
  toJSON cfg = Aeson.object
    [ "cfg-dir"      .= cfgDir       cfg
    , "grammars"     .= grammars     cfg
    , "courses"      .= coursesCfgs  cfg
    , "db"           .= db           cfg
    , "access-log"   .= accessLog    cfg
    , "error-log"    .= errorLog     cfg
    , "port"         .= port         cfg
    , "static-dir"   .= staticDir    cfg
    , "virtual-root" .= virtualRoot  cfg
    , "users"        .= users        cfg
    ]


data Course = Course Text FilePath
  
instance FromJSON Course where
  parseJSON = Aeson.withObject "Course" $ 
    \v -> Course <$> v .: "name" <*> v .: "path"

instance ToJSON Course where
  toJSON (Course name path) = Aeson.object [ "name" .= name, "path" .= path ]

  
data Grammar = Grammar
  { name :: Text
  , path :: FilePath
  , options :: GrammarOptions
  }

instance FromJSON Grammar where
  parseJSON = Aeson.withObject "Grammar" $ \v -> Grammar
    <$> v .: "name"
    <*> v .: "path"
    <*> v .: "options"

instance ToJSON Grammar where
  toJSON (Grammar n p o) = Aeson.object
    [ "name"    .= n
    , "path"    .= p
    , "options" .= o
    ]


data GrammarOptions = GrammarOptions
  { searchDepth :: Maybe Int
  , searchSize  :: Maybe Int
  }
  deriving (Show, Eq, Ord)

instance FromJSON GrammarOptions where
  parseJSON = Aeson.withObject "GrammarOptions" $ \v -> GrammarOptions
    <$> v .:? "search-depth"
    <*> v .:? "search-size"

instance ToJSON GrammarOptions where
  toJSON (GrammarOptions d s) = Aeson.object
    [ "search-depth" .= d
    , "search-size"  .= s
    ]


data InitialUser = User
  { name :: Text
  , pwd :: Text
  }

instance FromJSON InitialUser where
  parseJSON = Aeson.withObject "InitialUser" $ \v -> User
    <$> v .: "name"
    <*> v .: "pwd"

instance ToJSON InitialUser where
  toJSON (User n p) = Aeson.object
    [ "name" .= n
    , "pwd"  .= p
    ]
