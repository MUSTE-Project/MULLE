{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language
 OverloadedStrings,
 TemplateHaskell
#-}

module Main (main) where

import Prelude ()
import Muste.Prelude

import Snap
  ( SnapletInit, makeSnaplet, nestSnaplet, addRoutes
  , ConfigLog(ConfigFileLog)
  )
import qualified Snap as Snap
import qualified Snap.Util.FileServe as Snap (serveDirectory)
import System.IO.Error (catchIOError)
import System.FilePath (takeDirectory)
import System.Directory (createDirectoryIfMissing, getCurrentDirectory)
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as ByteString
import Data.Semigroup (Semigroup((<>)))
import qualified Data.Yaml as Yaml (encode)
import Control.Lens (makeLenses)

import qualified Muste.Web.Protocol as Protocol
import qualified Muste.Web.Config   as Config
import qualified Muste.Web.DbInit   as DbInit
import qualified Options

data App = App
  { _api    :: Snap.Snaplet Protocol.AppState
  , _static :: Snap.Snaplet ()
  }

makeLenses ''App

-- | Handler for api requests and serving file serving.
appInit :: Config.AppConfig -> SnapletInit App App
appInit cfg = makeSnaplet "muste" "Multi Semantic Text Editor"
  Nothing
  $ do
    api'    <- nestSnaplet (p "api")  api    (apiInit cfg)
    static' <- nestSnaplet (p mempty) static (staticInit cfg)
    pure $ App api' static'
  where
    p :: ByteString -> ByteString
    p = (ByteString.pack (Config.virtualRoot cfg) </>)

-- | Runs a static file server and the main api.  All requests to
-- @/api/*@ are handled by the API.  For the protocol refer to
-- @Protocol.apiRoutes@.  All other requests are handled as requests
-- for static files housed in @Config.demoDir@.
main :: IO ()
main = do
  opts <- Options.getOptions
  let cfgFile = Options.configFile opts
  cfg <- Config.appConfig cfgFile
  showConfig cfgFile cfg
  when (Options.initDb opts) (DbInit.initDb cfg)
  mapM_ mkParDir [Config.accessLog cfg, Config.errorLog cfg]
  (_, site, cleanup) <- Snap.runSnaplet Nothing (appInit cfg)
  Snap.httpServe (appConfig cfg) site `catchIOError` \err -> do
    cleanup
    ioError err

showConfig :: FilePath -> Config.AppConfig -> IO ()
showConfig cfgFile cfg = do
  getCurrentDirectory >>= printf "[Current Directory: %s]\n" 
  printf "[Reading configuration file: %s]\n\n" cfgFile
  printf $ ByteString.unpack $ Yaml.encode cfg
  printf "\n"

-- | @'mkParDir' p@ Ensure that the directory that @p@ is in is
-- created.
mkParDir :: FilePath -> IO ()
mkParDir = createDirectoryIfMissing True . takeDirectory

-- | The main configuration.
appConfig :: Config.AppConfig -> Snap.Config a b
appConfig cfg
    = Snap.setAccessLog (ConfigFileLog (Config.accessLog cfg))
    $ Snap.setErrorLog  (ConfigFileLog (Config.errorLog cfg))
    $ Snap.setPort      (Config.port cfg)
    $ mempty

-- | Serves static files in the @demo/@ directory.
staticInit :: Config.AppConfig -> SnapletInit a ()
staticInit cfg = makeSnaplet "static" "Static file server" Nothing $ do
  void $ addRoutes [("", Snap.serveDirectory (Config.staticDir cfg))]

apiInit :: Config.AppConfig -> SnapletInit a Protocol.AppState
apiInit cfg = Protocol.apiInit (Config.db cfg) (Config.lessons cfg)

(</>) :: IsString a => Semigroup a => a -> a -> a
a </> b = a <> "/" <> b
