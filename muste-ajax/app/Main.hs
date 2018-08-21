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
import System.IO.Error
import System.FilePath (takeDirectory)
import System.Directory (createDirectoryIfMissing)
import Data.String
import Snap.Util.CORS
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as ByteString
import Data.Semigroup (Semigroup((<>)))
import qualified Data.Yaml as Yaml (encode)

import qualified Protocol
import qualified Config
import qualified DbInit (initDb)
import qualified Options

-- | Runs a static file server and the main api.  All requests to
-- @/api/*@ are handled by the API.  For the protocol refer to
-- @Protocol.apiRoutes@.  All other requests are handled as requests
-- for static files housed in @Config.demoDir@.
main :: IO ()
main = do
  opts <- Options.getOptions
  showConfig
  when (Options.initDb opts) DbInit.initDb
  mapM_ mkParDir [Config.accessLog, Config.errorLog]
  (_, site, cleanup) <- Snap.runSnaplet Nothing appInit
  Snap.httpServe appConfig site `catchIOError` \err -> do
    cleanup
    ioError err

showConfig ∷ IO ()
showConfig = do
  printf "[Configurations options]\n"
  printf $ ByteString.unpack $ Yaml.encode $ Config.appConfig
  printf "\n"

-- | @'mkParDir' p@ Ensure that the directory that @p@ is in is
-- created.
mkParDir ∷ FilePath → IO ()
mkParDir = createDirectoryIfMissing True . takeDirectory

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
  Protocol.registerRoutes Config.db

-- | Serves static files in the @demo/@ directory.
staticInit :: SnapletInit a ()
staticInit = makeSnaplet "static" "Static file server" Nothing $ do
  void $ addRoutes [("", Snap.serveDirectory Config.staticDir)]

-- | Handler for api requests and serving file serving.
appInit :: SnapletInit b ()
appInit = makeSnaplet "muste" "Multi Semantic Text Editor"
  (Just (pure Config.wwwRoot))
  $ do
    void $ nestSnaplet (p "api")  (err "api")    apiInit
    void $ nestSnaplet (p mempty) (err "static") staticInit
  where
    p ∷ ByteString → ByteString
    p = (ByteString.pack Config.virtualRoot </>)
    err :: String -> a
    err s = error
      $ printf "Main.appInit: TODO: Missing lens for `%s`" s

(</>) ∷ IsString a ⇒ Semigroup a ⇒ a → a → a
a </> b = a <> "/" <> b
