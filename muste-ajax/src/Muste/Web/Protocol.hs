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
{-# Language CPP, RecordWildCards, UndecidableInstances, DeriveAnyClass,
  OverloadedLists #-}
{-# OPTIONS_GHC -Wall -Wcompat #-}
module Muste.Web.Protocol
  ( apiInit
  , AppState
  ) where

import           Prelude ()
import           Muste.Prelude
import qualified Muste.Prelude.SQL            as SQL
import           Muste.Prelude.SQL (Connection)

import           Data.ByteString (ByteString)
import qualified Data.Map                     as Map
import qualified Snap
import           Snap (MonadSnap)
import qualified Snap.Util.CORS               as Cors

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

openConnection ∷ MonadIO io ⇒ String → io Connection
openConnection p = do
  c ← liftIO $ SQL.open p
#ifdef DIAGNOSTICS
  liftIO $ SQL.setTrace c (Just Text.putStrLn)
#endif
  pure c

initApp
  ∷ MonadIO io
  ⇒ String
  → io AppState
initApp db = do
  liftIO  $ putStrLn "[Initializing app...]"
  conn    ← openConnection db
  ctxts   ← initContexts conn
  knownGs ← Grammar.noGrammars
  liftIO  $ putStrLn "[Initializing app... Done]"
  pure    $ AppState conn ctxts knownGs

initContexts ∷ MonadIO io ⇒ Connection → io Contexts
initContexts conn = Grammar.runGrammarT $ do
  c ← flip Database.runDbT conn $ do
    lessons ← Database.getLessons
    mkContexts lessons
  case c of
    Left e → liftIO $ throw e
    Right a → pure a

mkContexts
  ∷ MonadDB r m
  ⇒ Grammar.MonadGrammar m
  ⇒ [Database.Lesson]
  → m Contexts
mkContexts xs = Map.fromList <$> traverse mkContext xs

mkContext
  ∷ Grammar.MonadGrammar m
  ⇒ Database.Lesson
  → m (Text, Map.Map Sentence.Language Linearization.Context)
mkContext Database.Lesson{..} = do
  m ← Linearization.getLangAndContext nfo grammar
  pure (name, Map.mapKeys f m)
  where
  f ∷ Text → Sentence.Language
  f l = Sentence.Language (Sentence.Grammar grammar) l
  nfo ∷ Linearization.BuilderInfo
  nfo = Linearization.BuilderInfo
    { searchDepth = fromIntegral <$> searchLimitDepth
    , searchSize  = fromIntegral <$> searchLimitSize
    }

-- | The main api.  For the protocol see @Protocol.apiRoutes@.
apiInit ∷ String → Snap.SnapletInit a AppState
apiInit db = Snap.makeSnaplet "api" "MUSTE API" Nothing $ do
  Snap.wrapSite (Cors.applyCORS Cors.defaultOptions)
  registerRoutes db

-- I just realize that we're initializing the whole environment on
-- each connection, this is not necessary, we shuold be able to for
-- instance keep the database connection alive at all times.
registerRoutes ∷ String → Snap.Initializer v AppState AppState
registerRoutes db = do
  Snap.addRoutes apiRoutes
  initApp db

-- | Map requests to various handlers.
apiRoutes ∷ ∀ v . [(ByteString, Snap.Handler v AppState ())]
apiRoutes =
  [ "login"        |> Handlers.loginHandler
  , "logout"       |> Handlers.logoutHandler
  , "lessons"      |> Handlers.lessonsHandler
  , "lesson"       |> Handlers.lessonHandler
  , "menu"         |> Handlers.menuHandler
  , "create-user"  |> Handlers.createUserHandler
  , "change-pwd"   |> Handlers.changePwdHandler
  , "high-scores"  |> Handlers.highScoresHandler
  ]
  where
    (|>) ∷ ∀ txt json snap
      . ToJSON json
      ⇒ MonadSnap snap
      ⇒ Grammar.MonadGrammar snap
      ⇒ txt
      → ProtocolT snap (Response json)
      → (txt, snap ())
    t |> act = (t, runProtocolT act)
