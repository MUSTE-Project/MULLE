-- | Defines the endpoints that the API exposes.
--
-- Module      : Muste.Web.Protocol.Handlers
-- License     : Artistic License 2.0
-- Stability   : experimental
-- Portability : POSIX
--
-- This module delegates work to "Muste.Web.Database" that handles
-- accessing the stored data as well as invoking the core logic
-- defined in package @muste@.

{-# Language RecordWildCards, UndecidableInstances, DeriveAnyClass,
  OverloadedLists #-}
{-# OPTIONS_GHC -Wall -Wcompat #-}

module Muste.Web.Protocol.Handlers
  ( loginHandler
  , logoutHandler
  , lessonsHandler
  , lessonHandler
  , menuHandler
  , createUserHandler
  , changePwdHandler
  , highScoresHandler
  ) where

import           Prelude ()
import           Muste.Prelude
import           Muste.Prelude.Extra

import           Control.Monad.Reader
import           Data.Aeson
import           Data.Map (Map)
import qualified Data.Map.Lazy               as Map
import qualified Data.Set                    as Set
import           Data.Set (Set)
import qualified Snap
import qualified System.IO.Streams           as Streams
import qualified Data.List.NonEmpty as NonEmpty
import qualified GHC.Num as Math

import           Muste.Linearization (Context)
import           Muste.Tree (TTree)
import qualified Muste.Menu                  as Menu
import qualified Muste.Sentence              as Sentence
import           Muste.Sentence.Annotated (Annotated)
import qualified Muste.Sentence.Unannotated  as Unannotated
import           Muste.Sentence.Unannotated (Unannotated)

import qualified Muste.Web.Ajax              as Ajax
import qualified Muste.Web.Ajax              as Lesson ( Lesson(..) )
import qualified Muste.Web.Ajax              as ClientTree ( ClientTree(..) )
import qualified Muste.Web.Database          as Database
import qualified Muste.Web.Database.Types    as Database
import qualified Muste.Web.Database.Types    as Database.User ( User(..) )
import qualified Muste.Web.Database.Types
  as Database.UserLessonScore ( UserLessonScore(..) )
import qualified Muste.Web.Database.Types    as ActiveLessonForUser
  (ActiveLessonForUser(..))
import           Muste.Web.Protocol.Class
import           Muste.Web.Types.Score (Score)
import qualified Muste.Web.Types.Score       as Score

liftEither :: MonadError ProtocolError m => SomeException ~ e => Either e a -> m a
liftEither = either (throwError . SomeProtocolError) pure

createUserHandler :: MonadProtocol m => m (Response ())
createUserHandler = do
  Ajax.CreateUser{..} <- getMessage
  Database.addUser $ Database.CreateUser
    { name     = name
    , password = password
    , enabled  = True
    }
  pure mempty

-- | Change password of the user.  The user currently (as of this
-- writing) does not need to be authenticated to change their
-- password.  They must simply provide their old password which is
-- then checked against the database.
changePwdHandler :: MonadProtocol m => m (Response ())
changePwdHandler = do
  Ajax.ChangePassword{..} <- getMessage
  Database.changePassword Database.ChangePassword
    { name = name
    , oldPassword = oldPassword
    , newPassword = newPassword
    }
  pure mempty

throwApiError :: MonadProtocol m => ApiError -> m a
throwApiError = throwError . ProtocolApiError

-- | Reads the data from the request and deserializes from JSON.
getMessage :: forall json m . FromJSON json => MonadProtocol m => m json
getMessage = do
  s <- Snap.runRequestBody Streams.read >>= \case
    Nothing -> throwApiError ErrReadBody
    Just a -> pure $ convertString a
  case eitherDecode @json s of
    Left e  -> throwApiError $ DecodeError e
    Right a -> pure a

-- TODO Token should be set as an HTTP Unsafe.header.
-- | Gets the current session token.
getToken :: MonadProtocol m => m Database.Token
getToken = do
  m <- getTokenCookie
  case m of
    Just c -> pure $ Database.Token $ convertString $ Snap.cookieValue c
    Nothing -> throwApiError NoAccessToken

getTokenCookie :: MonadProtocol m => m (Maybe Snap.Cookie)
getTokenCookie = Snap.getCookie "LOGIN_TOKEN"

lessonsHandler :: MonadProtocol m => m (Response Ajax.LessonList)
lessonsHandler = do
  t <- getToken
  lessons <- getActiveLessons t
  pure <$> verifyMessage (Ajax.LessonList lessons)

getActiveLessons :: MonadProtocol m => Database.Token -> m [Ajax.ActiveLesson]
getActiveLessons t =
  fmap step . groupOn ActiveLessonForUser.lesson <$> Database.getActiveLessons t
  where
  step :: NonEmpty Database.ActiveLessonForUser -> Ajax.ActiveLesson
  step xs@(Database.ActiveLessonForUser{..} :| _) = Ajax.ActiveLesson
    { lesson        = lesson
    , name          = name
    , exercisecount = exercisecount
    , score         = sconcat <$> maybeScores
    -- This shuold be the same as asking whether 'score' is a 'Just'
    -- cell.
    , finished      = passedcount == exercisecount
    , enabled       = enabled
    , passedcount   = passedcount
    }
    where
    passedcount
      = fromIntegral
      $ length
      $ NonEmpty.filter isFinished xs
    isFinished :: Database.ActiveLessonForUser -> Bool
    isFinished = isJust . ActiveLessonForUser.score
    scores :: NonEmpty (Maybe Score)
    scores = ActiveLessonForUser.score <$> xs
    -- If just a single score is a Nothing we say that the score is a
    -- nothing.  Though they should all agree.
    maybeScores :: Maybe (NonEmpty Score)
    maybeScores = traverse identity scores

lessonHandler :: MonadProtocol m => m (Response Ajax.MenuResponse)
lessonHandler = Snap.method Snap.POST $ do
  l <- Snap.pathArg (pure . Database.Key @Database.Lesson)
  Ajax.StartLessonSettings restart <- getMessage @Ajax.StartLessonSettings
  when restart (resetLesson l)
  pure <$> handleLessonInit l

-- | Removes all finished exercises for the given lesson.
resetLesson
  :: MonadProtocol m
  => Database.Key Database.Lesson
  -> m ()
resetLesson l = do
  t <- getToken
  Database.resetLesson t l

menuHandler :: MonadProtocol m => m (Response Ajax.MenuResponse)
menuHandler = getMessage >>= fmap pure . handleMenuRequest

loginHandler :: MonadProtocol m => m (Response Ajax.LoginSuccess)
loginHandler = Snap.method Snap.POST
  $ getMessage >>= fmap pure . handleLoginRequest

logoutHandler :: MonadProtocol m => m (Response ())
logoutHandler
  = Snap.method Snap.POST
  $ getToken >>= handleLogoutRequest

setLoginCookie
  :: MonadProtocol m
  => Text -- ^ The token
  -> m ()
setLoginCookie tok
  = Snap.modifyResponse $ Snap.addResponseCookie c
  where
    c = Snap.Cookie "LOGIN_TOKEN" (convertString tok)
      Nothing Nothing (pure "/") False False

-- TODO I think we shouldn't be using sessions for this.  I think the
-- way to go is to use the basic http authentication *on every
-- request*.  That is, the client submits user/password on every
-- request.  Security is handled by SSL in the transport layer.
-- Further thought: Well, we're just sending the authentication token
-- in stead.  This one also cannot be spoofed.
handleLoginRequest
  :: MonadProtocol m
  => Ajax.LoginRequest
  -> m Ajax.LoginSuccess
handleLoginRequest Ajax.LoginRequest{..} = do
  user <- Database.authUser name password
  Database.Token token <- Database.startSession $ Database.User.key user
  setLoginCookie token
  pure $ Ajax.LoginSuccess token

askContexts :: MonadProtocol m => m Contexts
askContexts = asks contexts

handleLessonInit
  :: forall m . MonadProtocol m
  => Database.Key Database.Lesson
  -> m Ajax.MenuResponse
handleLessonInit lesson = do
  token <- getToken
  Database.ExerciseLesson{..} <- Database.startLesson token lesson
  menu <- assembleMenus $ AssembleMenu
    { lesson = lessonName
    , source = Ajax.ClientTree
      { sentence = source
      , direction = dir srcDir
      }
    , target = Ajax.ClientTree
      { sentence = target
      , direction = dir trgDir
      }
    }
  verifyMessage $ Ajax.MenuResponse
    { lesson = Ajax.Lesson
      { key  = lesson
      , name = lessonName
      }
    , score    = mempty
    , menu     = menu
    , lessonFinished = False
    -- Strictly speaking we can't know this for sure, but we'll just
    -- have a guess.
    , exerciseFinished = False
    , settings = Just $ Ajax.MenuSettings
      { highlightMatches = highlightMatches
      , showSourceSentence = showSourceSentence
      }
    }

dir :: Database.Direction -> Ajax.Direction
dir = \case
  Database.VersoRecto -> Ajax.VersoRecto
  Database.RectoVerso -> Ajax.RectoVerso

-- | This request is called after the user selects a new sentence from
-- the drop-down menu.  A request consists of two 'Ajax.ClientTree's
-- (the source and the target sentece) these can represent multiple
-- actual sentences ('TTree's).  We determine if the current exercise
-- is over by checking the source and target tree for equality.
-- 'Ajax.ClientTree's are considered equal in this case if they have
-- just one 'TTree' in common.  We respond to the caller whether the
-- exercise is over.  In either case we also return two new
-- 'Ajax.ClientTree's. For more information about what these contain
-- see the documentation there.
handleMenuRequest
  :: forall m . MonadProtocol m
  => Ajax.MenuRequest
  -> m Ajax.MenuResponse
handleMenuRequest Ajax.MenuRequest{..} = do
  let Ajax.Score{..}  = score
      Ajax.Lesson{..} = lesson
      lessonName = Lesson.name lesson
  verifySession
  token <- getToken
  let
    newScore
      = score
      & Score.addClick 1
      & Score.setTime time
  exerciseFinished <- oneSimiliarTree lessonName src trg
  lessonFinished   <- if exerciseFinished
    then Database.finishExercise token key newScore
    else pure False
  menu <- assembleMenus $ AssembleMenu
    { lesson = lessonName
    , source = src
    , target = trg
    }
  verifyMessage $ Ajax.MenuResponse
    { lesson           = lesson
    , score            = newScore
    , menu             = menu
    , lessonFinished   = lessonFinished
    , exerciseFinished = exerciseFinished
    , settings         = settings
    }

annotate
  :: MonadProtocol m
  => Text
  -> Unannotated
  -> m Annotated
annotate lesson s = do
  cs <- askContexts
  liftEither $ do
    ctxt <- getContext cs lesson $ l
    Unannotated.annotate
      (ErrorCall $ "Unable to parse: " <> show s) ctxt s
    where
    l :: Sentence.Language
    l = Sentence.language s

oneSimiliarTree
  :: forall m . MonadProtocol m
  => Text
  -> Ajax.ClientTree
  -> Ajax.ClientTree
  -> m Bool
oneSimiliarTree lesson src trg = do
  srcS <- parse src
  trgS <- parse trg
  pure $ oneInCommon srcS trgS
  where
  oneInCommon :: Ord a => Set a -> Set a -> Bool
  oneInCommon a b = not $ Set.null $ Set.intersection a b
  parse :: Ajax.ClientTree -> m (Set TTree)
  parse = fmap Set.fromList . disambiguate lesson

disambiguate
  :: forall m . MonadProtocol m
  => Text
  -> Ajax.ClientTree
  -> m [TTree]
disambiguate lesson Ajax.ClientTree{..} = do
  cs <- askContexts
  let
    getC :: Unannotated -> m Context
    getC u = liftEither $ getContext cs lesson (Sentence.language u)
  c <- getC sentence
  pure $ Sentence.disambiguate c sentence

handleLogoutRequest
  :: MonadProtocol m
  => Database.Token
  -> m (Response ())
handleLogoutRequest = fmap pure . Database.endSession

-- | @'verifySession' tok@ verifies the user identified by @tok@.
-- This method throws (using one of the error instances of
-- 'MonadProtocol') if the user is not authenticated.
verifySession :: MonadProtocol m => m ()
verifySession = getToken >>= Database.verifySession

-- | Returns the same message unmodified if the user is authenticated,
-- otherwise return 'SMSessionInvalid'.
verifyMessage :: MonadProtocol m => a -> m a
verifyMessage msg = msg <$ verifySession

data AssembleMenu = AssembleMenu
  { lesson :: Text
  , source :: Ajax.ClientTree
  , target :: Ajax.ClientTree
  }

-- | Gets the menus for a lesson.  This consists of a source tree and
-- a target tree.
assembleMenus
  :: MonadProtocol m
  => AssembleMenu
  -> m Ajax.MenuList
-- assembleMenus lesson sourceTree targetTree srcDir trgDir = do
assembleMenus AssembleMenu{..} = do
  c <- askContexts
  let mkTree = makeTree c lesson
  let ann = annotate lesson
  src <- ann $ ClientTree.sentence source
  trg <- ann $ ClientTree.sentence target
  pure $ Ajax.MenuList
    { src = mkTree src $ ClientTree.direction source
    , trg = mkTree trg $ ClientTree.direction target
    }

getContext
  :: MonadThrow m
  => Contexts
  -> Text              -- ^ Lesson
  -> Sentence.Language -- ^ Language
  -> m Context
getContext ctxts lesson s
  =   pure ctxts
  >>= lookupM (LessonNotFound lesson) lesson
  >>= lookupM (LanguageNotFound s) s

lookupM
  :: MonadThrow m
  => Exception e
  => Ord k
  => e -> k -> Map k a -> m a
lookupM err k = liftMaybe err . Map.lookup k

-- | Lift a 'Maybe' to any 'MonadThrow'.
liftMaybe :: MonadThrow m => Exception e => e -> Maybe a -> m a
liftMaybe e = \case
  Nothing -> throwM e
  Just a  -> pure a

-- | @'makeTree' ctxt lesson src trg tree@ Creates a 'ServerTree' from
-- a source trees and a target tree.  The 'Menu' is provided given
-- @tree@.
makeTree
  :: Contexts
  -> Text
  -> Annotated
  -> Ajax.Direction
  -> Ajax.ServerTree
makeTree c lesson s d
  = Ajax.ServerTree
  { sentence  = s
  , menu      = Menu.getMenu Menu.emptyPruneOpts ctxt (Sentence.linearization s)
  , direction = d
  }
  where
  ctxt = throwLeft $ getContext c lesson language
  language = Sentence.language s

highScoresHandler :: MonadProtocol m => m (Response [Ajax.HighScore])
highScoresHandler = pure . step <$> Database.getUserLessonScores
  where
  -- Group by lesson, then sort by the valuation of the score.
  step :: [Database.UserLessonScore] -> [Ajax.HighScore]
  step = NonEmpty.groupBy theLesson >>> fmap byValuation
  byValuation  = NonEmpty.sortBy theValuation >>> NonEmpty.head >>> go
  theLesson    = ((==) `on` Database.UserLessonScore.lesson)
  theValuation = compare `on` Math.negate . Score.valuation . Database.UserLessonScore.score
  go :: Database.UserLessonScore -> Ajax.HighScore
  go Database.UserLessonScore{..} = Ajax.HighScore
    { lesson = Ajax.Lesson
        { key  = lesson
        , name = lessonName
        }
    , user = Ajax.User
        { key  = user
        , name = userName
        }
    , score = score
    }

