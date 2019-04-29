{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language
 NamedFieldPuns,
 OverloadedStrings,
 ScopedTypeVariables
#-}

module Muste.Web.Protocol
  ( apiInit
  , AppState
  ) where

import Control.Exception (Exception(displayException), SomeException)
import qualified Control.Exception.Lifted as CL
import Control.Monad.IO.Class (MonadIO(liftIO))
import qualified Snap
import qualified Snap.Util.CORS as Cors
import System.FilePath ((</>)) 
import qualified System.IO.Streams as Streams

import qualified Database.SQLite.Simple as SQL

import qualified Data.Aeson as Aeson
import Data.Aeson (FromJSON, ToJSON, (.=))
import qualified Data.Yaml as Yaml
import Data.String.Conversions (convertString)
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as ByteString
import qualified Data.HashMap.Strict as HMap

import qualified Muste
import Muste (BuilderInfo(..))

import qualified Muste.Web.Config as Config
import Muste.Web.Config (AppConfig(..), Grammar(..))
import qualified Muste.Web.Protocol.Class as Proto
import Muste.Web.Protocol.Class (AppState(..), MULLE)

import qualified Muste.Web.Handlers.Session as Session
import qualified Muste.Web.Handlers.Results as Results
import qualified Muste.Web.Handlers.Grammar as Grammar


-- | The main api.  For the protocol see @Protocol.apiRoutes@.
apiInit :: Config.AppConfig -> Snap.SnapletInit a AppState
apiInit AppConfig{cfgDir, db, grammars, lessons}
  = Snap.makeSnaplet "api" "MUSTE API" Nothing
  $ do Snap.wrapSite (Cors.applyCORS Cors.defaultOptions)
       Snap.addRoutes apiRoutes
       liftIO $
         do putStrLn ">> Initializing app..."
            conn <- SQL.open $ cfgDir </> db
            let lessonsCfg = cfgDir </> lessons
            mustate <- Muste.loadGrammarsMU cfgDir Muste.emptyMUState
                       [ (name, path, binfo)
                       | Grammar{name, path, options} <- grammars,
                         let binfo = BuilderInfo
                               { searchDepth = fromIntegral <$> Config.searchDepth options 
                               , searchSize  = Config.searchSize options
                               }
                       ]
            putStrLn "<< Initializing app: OK\n"
            return $ AppState conn lessonsCfg mustate


-- | Map requests to various handlers.
apiRoutes :: [(ByteString, MULLE v ())]
apiRoutes =
  [ "login"                   |> Session.loginUser
  , "logout"                  |> Session.logoutUser
  , "create-user"             |> Session.createUser
  , "change-pwd"              |> Session.changePwd
  , "get-lessons"             |> Session.getAllLessons

  , "get-menus"               |> Grammar.getMenus
  , "get-edit-distance"       |> Grammar.editDistance

  , "add-completed-exercise"  |> Results.addCompletedExercise
  , "get-completed-exercises" |> Results.getCompletedExercises
  , "add-completed-lesson"    |> Results.addCompletedLesson
  , "get-completed-lessons"   |> Results.getCompletedLessons
  , "get-highscores"          |> Results.getHighscores

-- , "log" |> LoggingHandlers.log
  ]


(|>) :: (FromJSON inp, ToJSON inp, ToJSON out) =>
        ByteString -> (inp -> MULLE v out) -> (ByteString, MULLE v ())
t |> action = (t, handler)
  where
    handler
      = Cors.applyCORS Cors.defaultOptions 
      $ Snap.method Snap.POST 
      $ do Snap.modifyResponse $ Snap.setContentType "application/json"
           runMULLE
             `CL.catch` \(e :: Proto.MULLError) ->
             returnError (Proto.errorResponseCode e) (show e) (displayException e)
             `CL.catch` \(e' :: SomeException) ->
             returnError 500 ("GenericError" :: String) (displayException e')
    runMULLE
      = do msg <- getMessage
           logStdout ("<--- REQUEST: " ++ show t ++ "\n") "<---\n" msg
           result <- action msg
           logStdout "---> RESULT:\n" "--->\n" result
           Snap.writeLBS $ Aeson.encode result
    returnError code errid msg
      = do let errobj = Aeson.object [ "code" .= code, "error" .= errid, "message" .= msg ]
           logStdout ("<===> ERROR, REQUEST: " ++ show t ++ "\n") "<===>\n" errobj
           Snap.modifyResponse $ Snap.setResponseCode code
           Snap.writeLBS $ Aeson.encode errobj


getMessage :: FromJSON json => MULLE v json
getMessage = 
  do body <- Snap.runRequestBody Streams.read
     case body of
       Nothing -> CL.throwIO (Proto.RequestBodyError)
       Just a' ->
         case Aeson.eitherDecode (convertString a') of
           Left  e -> CL.throwIO (Proto.JSONDecodeError e)
           Right a -> return a


logStdout :: ToJSON json => String -> String -> json -> MULLE v ()
logStdout header footer obj
  = liftIO $ putStrLn $ header ++ body ++ footer
  where
    body = ByteString.unpack $ Yaml.encode $ transform $ Aeson.toJSON obj
    transform (Aeson.Object o) = Aeson.Object (HMap.mapWithKey trans' o)
    transform o = o
    trans' key val
      | key == "menus" = Aeson.String "<<MENUS>>"
      | otherwise = transform val
