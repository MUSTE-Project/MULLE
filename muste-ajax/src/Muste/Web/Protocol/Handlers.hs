{-# Language RecordWildCards, UndecidableInstances, DeriveAnyClass,
  OverloadedLists #-}
{-# OPTIONS_GHC -Wall -Wcompat #-}
module Muste.Web.Protocol.Handlers
  (
    loginHandler
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

import qualified Muste
import           Muste (Context, TTree)
import qualified Muste.Menu                  as Menu
import qualified Muste.Sentence              as Sentence
import           Muste.Sentence.Annotated (Annotated)
import qualified Muste.Sentence.Unannotated  as Unannotated
import           Muste.Sentence.Unannotated (Unannotated)

import qualified Muste.Web.Ajax              as Ajax
import           Muste.Web.Ajax (ClientTree, ServerTree)
import qualified Muste.Web.Database          as Database
import qualified Muste.Web.Database.Types    as Database
import           Muste.Web.Protocol.Class
import qualified Muste.Web.Types.Score       as Score
import           Muste.Web.Types.Score (Score(Score))

liftEither ∷ MonadError ProtocolError m ⇒ SomeException ~ e ⇒ Either e a → m a
liftEither = either (throwError . SomeProtocolError) pure

createUserHandler ∷ MonadProtocol m ⇒ m (Response ())
createUserHandler = do
  Ajax.User{..} ← getMessage
  Database.addUser name password True
  pure mempty

-- | Change password of the user.  The user currently (as of this
-- writing) does not need to be authenticated to change their
-- password.  They must simply provide their old password which is
-- then checked against the database.
changePwdHandler ∷ MonadProtocol m ⇒ m (Response ())
changePwdHandler = do
  Ajax.ChangePwd{..} ← getMessage
  Database.changePassword name oldPassword newPassword
  pure mempty

throwApiError ∷ MonadProtocol m ⇒ ApiError → m a
throwApiError = throwError . ProtocolApiError

-- | Reads the data from the request and deserializes from JSON.
getMessage ∷ ∀ json m . FromJSON json ⇒ MonadProtocol m => m json
getMessage = do
  s ← Snap.runRequestBody Streams.read >>= \case
    Nothing → throwApiError ErrReadBody
    Just a → pure $ convertString a
  case eitherDecode @json s of
    Left e  → throwApiError $ DecodeError e
    Right a → pure a

-- TODO Token should be set as an HTTP Unsafe.header.
-- | Gets the current session token.
getToken :: MonadProtocol m ⇒ m Text
getToken = do
  m <- getTokenCookie
  case m of
    Just c -> pure $ convertString $ Snap.cookieValue c
    Nothing -> throwApiError NoAccessToken

getTokenCookie :: MonadProtocol m ⇒ m (Maybe Snap.Cookie)
getTokenCookie = Snap.getCookie "LOGIN_TOKEN"


-- * Handlers
lessonsHandler :: MonadProtocol m ⇒ m (Response Ajax.LessonList)
lessonsHandler = do
  t ← getToken
  lessons ← Database.getActiveLessons t
  pure <$> verifyMessage (Ajax.LessonList lessons)

lessonHandler ∷ MonadProtocol m ⇒ m (Response Ajax.MenuResponse)
lessonHandler = pure <$> Snap.pathArg (handleLessonInit . Database.Key)

menuHandler ∷ MonadProtocol m ⇒ m (Response Ajax.MenuResponse)
menuHandler = getMessage >>= fmap pure . handleMenuRequest

loginHandler :: MonadProtocol m ⇒ m (Response Ajax.LoginSuccess)
loginHandler = Snap.method Snap.POST
  $ getMessage >>= fmap pure . handleLoginRequest

logoutHandler ∷ MonadProtocol m ⇒ m (Response ())
logoutHandler
  = Snap.method Snap.POST
  $ getToken >>= fmap pure . handleLogoutRequest

setLoginCookie
  :: MonadProtocol m
  => Text -- ^ The token
  -> m ()
setLoginCookie tok = Snap.modifyResponse $ Snap.addResponseCookie c
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
  ∷ MonadProtocol m
  ⇒ Ajax.LoginRequest
  → m Ajax.LoginSuccess
handleLoginRequest Ajax.LoginRequest{..} = do
  Database.authUser username password
  token ← Database.startSession username
  setLoginCookie token
  pure $ Ajax.LoginSuccess token

askContexts :: MonadProtocol m ⇒ m Contexts
askContexts = asks contexts

handleLessonInit
  ∷ ∀ m
  . MonadProtocol m
  ⇒ Database.Key -- ^ Lesson
  → m Ajax.MenuResponse
handleLessonInit lesson = do
  token ← getToken
  Database.ExerciseLesson{..} ← Database.startLesson token lesson
  menu ← assembleMenus lessonName source target
  verifyMessage $ Ajax.MenuResponse
    { key      = lesson
    , lesson   = lessonName
    , score    = mempty
    , menu     = Just menu
    , finished = False
    }

-- | This request is called after the user selects a new sentence from
-- the drop-down menu.  A request consists of two 'ClientTree's (the
-- source and the target sentece) these can represent multiple actual
-- sentences ('TTree's).  We determine if the current exercise is over
-- by checking the source and target tree for equality.  'ClientTree's
-- are considered equal in this case if they have just one 'TTree' in
-- common.  We respond to the caller whether the exercise is over.  In
-- either case we also return two new 'ClientTree's -- these are used
-- if the exercise continues.  For more information about what these
-- contain see the documentation there.
handleMenuRequest
  ∷ ∀ m
  . MonadProtocol m
  ⇒ Ajax.MenuRequest
  → m Ajax.MenuResponse
handleMenuRequest Ajax.MenuRequest{..} = do
  let Score{..} = score
  verifySession
  token ← getToken
  let
    newScore
      = score
      & Score.addClick 1
      & Score.setTime time
  finished ← oneSimiliarTree lesson src trg
  (lessonFinished, menu) ←
    if finished
    then do
      f ← Database.finishExercise token key newScore
      pure (f, Nothing)
    else do
      m ← assembleMenus lesson (un src) (un trg)
      pure (False, Just m)
  verifyMessage $ Ajax.MenuResponse
    { key      = key
    , lesson   = lesson
    , score    = newScore
    , menu     = menu
    , finished = lessonFinished
    }
  where
  un (Ajax.ClientTree t) = t

annotate
  ∷ MonadProtocol m
  ⇒ Text
  → Unannotated
  → m Annotated
annotate lesson s = do
  cs ← askContexts
  liftEither $ do
    ctxt ← getContext cs lesson $ l
    Unannotated.annotate
      (ErrorCall $ "Unable to parse: " <> show s) ctxt s
    where
    l ∷ Sentence.Language
    l = Sentence.language s

oneSimiliarTree
  ∷ ∀ m
  . MonadProtocol m
  ⇒ Text
  → ClientTree
  → ClientTree
  → m Bool
oneSimiliarTree lesson src trg = do
  srcS ← parse src
  trgS ← parse trg
  pure $ oneInCommon srcS trgS
  where
  oneInCommon ∷ Ord a ⇒ Set a → Set a → Bool
  oneInCommon a b = not $ Set.null $ Set.intersection a b
  parse ∷ ClientTree → m (Set TTree)
  parse = fmap Set.fromList . disambiguate lesson

disambiguate
  ∷ ∀ m
  . MonadProtocol m
  ⇒ Text
  → ClientTree
  → m [TTree]
disambiguate lesson (Ajax.ClientTree t) = do
  cs ← askContexts
  let
    getC ∷ Unannotated → m Context
    getC u = liftEither $ getContext cs lesson (Sentence.language u)
  c ← getC t
  pure $ Sentence.disambiguate c t

handleLogoutRequest ∷ MonadProtocol m ⇒ Text → m ()
handleLogoutRequest = Database.endSession

-- | @'verifySession' tok@ verifies the user identified by @tok@.
-- This method throws (using one of the error instances of
-- 'MonadProtocol') if the user is not authenticated.
verifySession ∷ MonadProtocol m ⇒ m ()
verifySession = getToken >>= Database.verifySession

-- | Returns the same message unmodified if the user is authenticated,
-- otherwise return 'SMSessionInvalid'.
verifyMessage ∷ MonadProtocol m ⇒ a → m a
verifyMessage msg = msg <$ verifySession

-- | Gets the menus for a lesson.  This consists of a source tree and
-- a target tree.
assembleMenus
  ∷ MonadProtocol m
  ⇒ Text
  → Unannotated
  → Unannotated
  → m Ajax.MenuList
assembleMenus lesson sourceTree targetTree = do
  c ← askContexts
  let mkTree = makeTree c lesson
  let ann = annotate lesson
  src ← ann sourceTree
  trg ← ann targetTree
  pure $ Ajax.MenuList
    { src = mkTree src
    , trg = mkTree trg
    }

getContext
  ∷ MonadThrow m
  ⇒ Contexts
  → Text              -- ^ Lesson
  → Sentence.Language -- ^ Language
  → m Context
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
  ∷ Contexts
  → Text
  → Annotated
  → ServerTree
makeTree c lesson s
  = Ajax.ServerTree s menu
  where
  menu = Muste.getMenu (mempty @Menu.PruneOpts) ctxt (Sentence.linearization s)
  ctxt = throwLeft $ getContext c lesson language
  language = Sentence.language s

highScoresHandler ∷ MonadProtocol m ⇒ m (Response [Ajax.HighScore])
highScoresHandler = do
  xs ← Database.getUserExerciseScores
  verifyMessage $ pure $ go xs
  where
  go ∷ [Database.UserExerciseScore] → [Ajax.HighScore]
  go = error "Muste.Web.Protocol.highScoresHandler: TODO Not implemented!"
