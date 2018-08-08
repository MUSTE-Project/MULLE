{-# language OverloadedStrings, UnicodeSyntax #-}
module Main (main) where

import Control.Monad
import Text.Printf
import Snap
  ( SnapletInit, makeSnaplet, nestSnaplet, addRoutes
  , ConfigLog(ConfigFileLog)
  )
import qualified Snap as Snap
import qualified Snap.Util.FileServe as Snap (serveDirectory)
import qualified Snap.Http.Server as Snap
import System.IO.Error
import Control.Monad.IO.Class (liftIO)
import Data.String
import Snap.Util.CORS
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as ByteString
import Data.Semigroup (Semigroup((<>)))
import qualified Data.Yaml as Yaml (encode)

import qualified Protocol
import qualified Config

-- | Runs a static file server and the main api.  All requests to
-- @/api/*@ are handled by the API.  For the protocol refer to
-- @Protocol.apiRoutes@.  All other requests are handled as requests
-- for static files housed in @Config.demoDir@.
main :: IO ()
main = do
  showConfig
  (_, site, cleanup) <- Snap.runSnaplet Nothing appInit
  Snap.httpServe appConfig site `catchIOError` \err -> do
    cleanup
    ioError err

showConfig ∷ IO ()
showConfig = do
  printf "[Configurations options]\n"
  printf $ ByteString.unpack $ Yaml.encode $ Config.appConfig

-- instance IsString ConfigLog where
--   fromString = ConfigFileLog

-- | The main configuration.
appConfig :: Snap.Config a b
appConfig
    = Snap.setAccessLog (ConfigFileLog Config.accessLog)
    $ Snap.setErrorLog  (ConfigFileLog Config.errorLog)
    $ Snap.setPort      Config.port
    $ mempty

-- | The main api.  For the protocol see @Protocol.apiRoutes@.
apiInit :: SnapletInit a ()
apiInit = makeSnaplet "api" "MUSTE API" Nothing $ do
  Snap.wrapSite (applyCORS defaultOptions)
  void $ addRoutes Protocol.apiRoutes

-- TODO Move @demo@ dir to @static@.
-- | Serves static files in the @demo/@ directory.
staticInit :: SnapletInit a ()
staticInit = makeSnaplet "static" "Static file server" Nothing $ do
  void $ addRoutes [("", Snap.serveDirectory Config.staticDir)]

-- | Handler for api requests and serving file serving.
appInit :: SnapletInit b ()
appInit = makeSnaplet "muste" "Multi Semantic Text Editor"
  (Just (pure Config.wwwRoot))
  $ void $ do
    -- TODO Missing lenses.  Dunno what they are used for though.
    nestSnaplet (p "api")  (err "api")    apiInit
    nestSnaplet (p mempty) (err "static") staticInit
  where
    p ∷ ByteString → ByteString
    p = (ByteString.pack Config.virtualRoot </>)
    err :: String -> a
    err s = error
      $ printf "Main.appInit: TODO: Missing lens for `%s`" s

(</>) ∷ IsString a ⇒ Semigroup a ⇒ a → a → a
a </> b = a <> "/" <> b
