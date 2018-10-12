{-# Language RecordWildCards, UndecidableInstances, DeriveAnyClass,
  OverloadedLists #-}
{-# OPTIONS_GHC -Wall -Wcompat #-}
module Muste.Web.Protocol
  ( apiInit
  , AppState
  ) where

import           Prelude ()
import           Muste.Prelude
import           Muste.Prelude.SQL (Connection)
import qualified Muste.Prelude.SQL            as SQL

import qualified Data.Map as Map
import           Data.ByteString (ByteString)
import           Snap (MonadSnap)
import qualified Snap
import qualified Snap.Util.CORS               as Cors
import qualified Data.Text.IO                 as Text

import qualified Muste
import           Muste (Context)
import qualified Muste.Sentence as Sentence
import qualified Muste.Linearization as Linearization

import           Muste.Web.Database (MonadDB)
import qualified Muste.Web.Database           as Database
import qualified Muste.Web.Database.Types     as Database
import           Muste.Web.Protocol.Class
import qualified Muste.Web.Protocol.Handlers  as Handlers

openConnection ∷ MonadIO io ⇒ String → io Connection
openConnection p = do
  c ← liftIO $ SQL.open p
  setTraceSql c
  pure c

setTraceSql ∷ MonadIO io ⇒ Connection → io ()
setTraceSql c = liftIO $ SQL.setTrace c (Just Text.putStrLn)

initApp
  ∷ MonadIO io
  ⇒ String
  → io AppState
initApp db = do
  liftIO  $ putStrLn "Initializing app..."
  conn    ← openConnection db
  ctxts   ← initContexts conn
  knownGs ← Muste.noGrammars
  liftIO  $ putStrLn "Initializing app... Done"
  pure    $ AppState conn ctxts knownGs

initContexts ∷ MonadIO io ⇒ Connection → io Contexts
initContexts conn = Muste.runGrammarT $ do
  c ← flip Database.runDbT conn $ do
    lessons ← Database.getLessons
    mkContexts lessons
  case c of
    Left e → liftIO $ throw e
    Right a → pure a

mkContexts
  ∷ MonadDB r m
  ⇒ Muste.MonadGrammar m
  ⇒ [Database.Lesson]
  → m Contexts
mkContexts xs = Map.fromList <$> traverse mkContext xs

mkContext
  ∷ Muste.MonadGrammar m
  ⇒ Database.Lesson
  → m (Text, Map.Map Sentence.Language Context)
mkContext Database.Lesson{..} = do
  m ← Muste.getLangAndContext nfo grammar
  pure $ (name, Map.mapKeys f m)
  where
  f ∷ Text → Sentence.Language
  f l = Sentence.Language (Sentence.Grammar grammar) l
  nfo ∷ Linearization.BuilderInfo
  nfo = Linearization.BuilderInfo
    { searchDepth = searchLimitDepth
    , searchSize  = searchLimitSize
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
      ⇒ Muste.MonadGrammar snap
      ⇒ txt
      → ProtocolT snap (Response json)
      → (txt, snap ())
    t |> act = (t, runProtocolT act)
