{-# language OverloadedStrings #-}
module Main (main) where

import Control.Monad
import Text.Printf
import Snap hiding (setPort)
import Snap.Util.FileServe (serveDirectory)
import Snap.Http.Server
import System.IO.Error
import Control.Monad.IO.Class (liftIO)
import Data.String
import Snap.Util.CORS
import qualified Protocol
import qualified Config

-- | Runs a static file server and the main api.  All requests to
-- @/api/*@ are handled by the API.  For the protocol refer to
-- @Protocol.apiRoutes@.  All other requests are handled as requests
-- for static files housed in @Config.demoDir@.
main :: IO ()
main = do
  (_, site, cleanup) <- runSnaplet Nothing appInit
  cfg <- getCfg
  httpServe cfg site `catchIOError` \err -> do
    cleanup
    ioError err

instance IsString ConfigLog where
  fromString = ConfigFileLog

-- | The main configuration.
getCfg :: IO (Config a b)
getCfg = do
  accessLog <- fromString <$> Config.getAccessLog
  errorLog  <- fromString <$> Config.getErrorLog
  pure
    $ setAccessLog accessLog
    $ setErrorLog  errorLog
    $ setPort      Config.port
    $ mempty

-- | The main api.  For the protocol see @Protocol.apiRoutes@.
apiInit :: SnapletInit a ()
apiInit = makeSnaplet "api" "MUSTE API" Nothing $ do
  wrapSite (applyCORS defaultOptions)
  void $ addRoutes Protocol.apiRoutes

-- TODO Move @demo@ dir to @static@.
-- | Serves static files in the @demo/@ directory.
staticInit :: SnapletInit a ()
staticInit = makeSnaplet "static" "Static file server" Nothing $ do
  dir <- liftIO Config.getStaticDir
  void $ addRoutes [("", serveDirectory dir)]

-- | Handler for api requests and serving file serving.
appInit :: SnapletInit b ()
appInit = makeSnaplet "muste" "Multi Semantic Text Editor" Nothing
  $ void $ do
    -- TODO Missing lenses.  Dunno what they are used for though.
    nestSnaplet "api"  (err "api")    apiInit
    nestSnaplet mempty (err "static") staticInit
  where
    err :: String -> a
    err s = error
      $ printf "Main.appInit: Missing lens for `%s`" s
