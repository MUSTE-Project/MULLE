-- | This module hooks 'ProtocolT' up with the @snap@ web framework.
--
-- Module      : Muste.Web.Protocol
-- License     : Artistic License 2.0
-- Stability   : experimental
-- Portability : POSIX
--
-- The inner workings of the protocol is defined in
--
--  * "Muste.Web.Protocol.Class"
--
-- The various handlers are defined in
--
--  * "Muste.Web.Protocol.Handlers"
--
{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language
 DeriveAnyClass,
 FlexibleContexts,
 OverloadedStrings,
 RecordWildCards,
 UndecidableInstances
#-}

module Muste.Web.Protocol
  ( apiInit
  , AppState
  ) where

import Control.Exception (throw)
import Control.Monad.Except (throwError)
import Control.Monad.IO.Class (MonadIO(liftIO))
import qualified Snap
import qualified Snap.Util.CORS as Cors
import qualified System.IO.Streams as Streams

import qualified Database.SQLite.Simple as SQL

import Data.Aeson (FromJSON)
import Data.String.Conversions (convertString)
import Data.Text (Text)

import Data.ByteString (ByteString)
import qualified Data.Map as Map
import qualified Data.Aeson as Aeson

import Muste (MUSTE, runMUSTE)
import qualified Muste

import qualified Muste.Web.Database as Database
import qualified Muste.Web.Database.Types as Database
import Muste.Web.Protocol.Class
import qualified Muste.Web.Protocol.Handlers as Handlers


-- | The main api.  For the protocol see @Protocol.apiRoutes@.
apiInit :: FilePath -> FilePath -> Snap.SnapletInit a AppState
apiInit db lessons
  = Snap.makeSnaplet "api" "MUSTE API" Nothing
  $ initializer db lessons


initializer :: FilePath -> FilePath -> Snap.Initializer v AppState AppState
initializer db lessons
  = do liftIO $ putStrLn "[Initializing app...]"
       Snap.wrapSite (Cors.applyCORS Cors.defaultOptions)
       Snap.addRoutes apiRoutes
       conn  <- liftIO $ SQL.open db
       ctxts <- liftIO $ runMUSTE $ initContexts conn
       liftIO $ putStrLn "[Initializing app... Done]"
       return $ AppState conn ctxts lessons


initContexts :: SQL.Connection -> MUSTE Contexts
initContexts conn
  = do lessons' <- Database.runDbT Database.getLessons conn
       case lessons' of
         Left err -> throw err
         Right lessons -> 
           do cxtlist <- traverse mkContext lessons
              return $ Map.fromList cxtlist


mkContext :: Database.Lesson -> MUSTE (Text, Map.Map Muste.Language Muste.Context)
mkContext Database.Lesson{..}
  = do m <- Muste.getLangAndContext nfo grammar
       return (name, Map.mapKeys (Muste.Language grammar) m)
  where
    nfo = Muste.BuilderInfo
      { searchDepth = fromIntegral <$> searchLimitDepth
      , searchSize  = fromIntegral <$> searchLimitSize
      }


-- | Map requests to various handlers.
apiRoutes :: [(ByteString, Snap.Handler v AppState ())]
apiRoutes =
  [ "login"        |> Handlers.handleLoginRequest
  , "logout"       |> Handlers.handleLogoutRequest
  , "lessons"      |> Handlers.handleLessons
  , "lesson"       |> Handlers.handleLessonInit
  , "menu"         |> Handlers.handleMenuRequest
  , "create-user"  |> Handlers.handleCreateUser
  , "change-pwd"   |> Handlers.handleChangePwd
  , "high-scores"  |> Handlers.handleHighScores
  ]
  where
    t |> action = (t, runProtocolT $
                      Snap.method Snap.POST $
                      do msg <- getMessage
                         fmap pure (action msg)
                  )


-- | Reads the data from the request and deserializes from JSON.
getMessage :: FromJSON json => MULLE v json
getMessage = 
  do s <- do body <- Snap.runRequestBody Streams.read
             case body of
               Nothing -> throwError (ProtocolApiError ErrReadBody)
               Just  a -> return (convertString a)
     case Aeson.eitherDecode s of
       Left  e -> throwError (ProtocolApiError (DecodeError e))
       Right a -> return a
