{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# language OverloadedStrings, UnicodeSyntax, TemplateHaskell #-}
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
import System.Directory (createDirectoryIfMissing)
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as ByteString
import Data.Semigroup (Semigroup((<>)))
import qualified Data.Yaml as Yaml (encode)
import Control.Lens (makeLenses)

import qualified Muste.Web.Protocol as Protocol
import qualified Muste.Web.Config   as Config

import qualified DbInit
import qualified Options

data App = App
  { _api    ∷ Snap.Snaplet Protocol.AppState
  , _static ∷ Snap.Snaplet ()
  }

makeLenses ''App

-- | Handler for api requests and serving file serving.
appInit ∷ SnapletInit App App
appInit = makeSnaplet "muste" "Multi Semantic Text Editor"
  Nothing
  $ do
    api'    ← nestSnaplet (p "api")  api    apiInit
    static' ← nestSnaplet (p mempty) static staticInit
    pure $ App api' static'
  where
    p ∷ ByteString → ByteString
    p = (ByteString.pack Config.virtualRoot </>)

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

-- | Serves static files in the @demo/@ directory.
staticInit :: SnapletInit a ()
staticInit = makeSnaplet "static" "Static file server" Nothing $ do
  void $ addRoutes [("", Snap.serveDirectory Config.staticDir)]

apiInit ∷ SnapletInit a Protocol.AppState
apiInit = Protocol.apiInit Config.db

(</>) ∷ IsString a ⇒ Semigroup a ⇒ a → a → a
a </> b = a <> "/" <> b
