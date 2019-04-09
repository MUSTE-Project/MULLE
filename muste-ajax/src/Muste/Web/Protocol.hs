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
 CPP,
 DeriveAnyClass,
 FlexibleContexts,
 OverloadedLists,
 OverloadedStrings,
 RecordWildCards,
 ScopedTypeVariables,
 UndecidableInstances
#-}

module Muste.Web.Protocol
  ( apiInit
  , AppState
  ) where

import           Prelude ()
import           Muste.Prelude

import qualified Database.SQLite.Simple as SQL

import           Data.ByteString (ByteString)
import qualified Data.Map                     as Map
import qualified Data.Aeson                   as Aeson
import qualified Snap
import qualified Snap.Util.CORS               as Cors
import qualified System.IO.Streams            as Streams

#ifdef DIAGNOSTICS
import qualified Data.Text.IO                 as Text
#endif

import qualified Muste.Grammar                as Grammar
import qualified Muste.Linearization          as Linearization
import qualified Muste.Sentence               as Sentence

import qualified Muste.Web.Database           as Database
import           Muste.Web.Database (MonadDB)
import qualified Muste.Web.Database.Types     as Database
import           Muste.Web.Protocol.Class
import qualified Muste.Web.Protocol.Handlers  as Handlers

openConnection :: MonadIO io => String -> io SQL.Connection
openConnection p = do
  c <- liftIO $ SQL.open p
#ifdef DIAGNOSTICS
  liftIO $ SQL.setTrace c (Just Text.putStrLn)
#endif
  pure c

initApp :: MonadIO io => FilePath -> FilePath -> io AppState
initApp db lessons = do
  liftIO  $ putStrLn "[Initializing app...]"
  conn    <- openConnection db
  ctxts   <- initContexts conn
  knownGs <- Grammar.noGrammars
  liftIO  $ putStrLn "[Initializing app... Done]"
  pure    $ AppState conn ctxts knownGs lessons

initContexts :: MonadIO io => SQL.Connection -> io Contexts
initContexts conn = Grammar.runGrammarT $ do
  c <- flip Database.runDbT conn $ do
    lessons <- Database.getLessons
    mkContexts lessons
  case c of
    Left e -> liftIO $ throw e
    Right a -> pure a

mkContexts
  :: MonadDB r m
  => Grammar.MonadGrammar m
  => [Database.Lesson]
  -> m Contexts
mkContexts xs = Map.fromList <$> traverse mkContext xs

mkContext
  :: Grammar.MonadGrammar m
  => Database.Lesson
  -> m (Text, Map.Map Sentence.Language Linearization.Context)
mkContext Database.Lesson{..} = do
  m <- Linearization.getLangAndContext nfo grammar
  pure (name, Map.mapKeys f m)
  where
  f :: Text -> Sentence.Language
  f l = Sentence.Language (Sentence.Grammar grammar) l
  nfo :: Linearization.BuilderInfo
  nfo = Linearization.BuilderInfo
    { searchDepth = fromIntegral <$> searchLimitDepth
    , searchSize  = fromIntegral <$> searchLimitSize
    }

-- | The main api.  For the protocol see @Protocol.apiRoutes@.
apiInit :: FilePath -> FilePath -> Snap.SnapletInit a AppState
apiInit db lessons = Snap.makeSnaplet "api" "MUSTE API" Nothing $ do
  Snap.wrapSite (Cors.applyCORS Cors.defaultOptions)
  registerRoutes db lessons


registerRoutes :: FilePath -> FilePath -> Snap.Initializer v AppState AppState
registerRoutes db lessons = do
  Snap.addRoutes apiRoutes
  initApp db lessons

-- | Map requests to various handlers.
apiRoutes :: forall v . [(ByteString, Snap.Handler v AppState ())]
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
getMessage :: (FromJSON json, MonadProtocol m) => m json
getMessage = 
  do s <- do body <- Snap.runRequestBody Streams.read
             case body of
               Nothing -> throwError (ProtocolApiError ErrReadBody)
               Just  a -> return (convertString a)
     case Aeson.eitherDecode s of
       Left  e -> throwError (ProtocolApiError (DecodeError e))
       Right a -> return a
