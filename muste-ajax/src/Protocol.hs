{-# Language RecordWildCards, UndecidableInstances, DeriveAnyClass #-}
{-# OPTIONS_GHC -Wall -Wno-orphans #-}
module Protocol
  ( registerRoutes
  ) where

import Prelude ()
import Muste.Prelude

import Data.Aeson
import Data.Map (Map)
import qualified Data.Map.Lazy as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Database.SQLite.Simple (Connection)
import qualified Database.SQLite.Simple as SQL
import Control.Monad.Reader
import Control.Monad.Except (MonadError(..), ExceptT, runExceptT)
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C8
import Snap (MonadSnap)
import qualified Snap
import qualified System.IO.Streams as Streams
import qualified Data.Text.Encoding as T
import Data.Time
import Control.Monad.Catch (MonadThrow(throwM))
import Control.Exception
  (Exception, ErrorCall(ErrorCall))
import Control.Monad.Trans.Control (MonadBaseControl)
import Control.Monad.Base (MonadBase)
import Data.String.Conversions (convertString)

import Muste (Context, TTree)
import qualified Muste
import qualified Muste.Sentence as Sentence
import Muste.Sentence.Annotated (Annotated)
import Muste.Sentence.Unannotated (Unannotated)
import qualified Muste.Sentence.Unannotated as Unannotated
import qualified Muste.Menu as Menu
import qualified Muste.Linearization as Linearization

import Common

import Ajax
  ( ServerMessage(..), ClientMessage(..)
  , ClientTree(..), ServerTree, User(..)
  , ChangePwd(..)
  )
import qualified Ajax
import Database (MonadDB, getConnection, MonadDatabaseError(..))
import qualified Database
import qualified Database.Types as Database

-- | Maps a lesson to a map from grammars(-identifiers) to their
-- corresponding contexts.
type Contexts = Map Text (Map Sentence.Language Context)

-- | The data needed for responding to requests.
data Env = Env
  { connection :: Connection
  , contexts   :: Contexts
  }

-- | A simple monad transformer for handling responding to requests.
newtype ProtocolT m a = ProtocolT
  { unProtocolT ∷ ReaderT Env (ExceptT ProtocolError m) a
  }

deriving newtype instance Functor m ⇒ Functor (ProtocolT m)
deriving newtype instance Monad m ⇒ Applicative (ProtocolT m)
deriving newtype instance Monad m ⇒ Monad (ProtocolT m)
deriving newtype instance MonadIO m ⇒ MonadIO (ProtocolT m)
deriving newtype instance MonadBaseControl IO m ⇒ MonadBaseControl IO (ProtocolT m)
deriving newtype instance MonadBase IO m ⇒ MonadBase IO (ProtocolT m)
deriving newtype instance MonadPlus m ⇒ MonadPlus (ProtocolT m)
deriving newtype instance Monad m ⇒ Alternative (ProtocolT m)
deriving newtype instance (MonadSnap m) ⇒ MonadSnap (ProtocolT m)
deriving newtype instance Monad m ⇒ MonadReader Env (ProtocolT m)
deriving newtype instance Monad m ⇒ Database.HasConnection (ProtocolT m)
deriving newtype instance Monad m ⇒ MonadError ProtocolError (ProtocolT m)

instance Monad m ⇒ MonadDatabaseError (ProtocolT m) where
  throwDbError = ProtocolT . throwError . DatabaseError
  -- | Only handles the database error.
  catchDbError (ProtocolT act) h
    = ProtocolT $ catchError act (unProtocolT . h')
    where
    -- The "demoted" handler.
    h' = \case
      DatabaseError err → h err
      e                 → ProtocolT $ throwError e

liftEither ∷ MonadError ProtocolError m ⇒ SomeException ~ e ⇒ Either e a → m a
liftEither = either (throwError . SomeProtocolError) pure

data ProtocolError
  = DatabaseError Database.Error
  -- This is needed to make this a monoid to in turn make ProtocolT a
  -- monadplus as requested by monadsnap.  Don't use this!  Better to
  -- use 'SomeProtocolError' or even better, add a constructor.
  | UnspecifiedError
  | ∀ e . Exception e ⇒ SomeProtocolError e
  | MissingApiRoute String
  | NoCookie
  | BadRequest
  | SessionInvalid
  | LoginFail

deriving stock instance Show ProtocolError
instance Exception ProtocolError where
  displayException = \case
    DatabaseError err → "A database error occurred: " <> displayException err
    UnspecifiedError  → "Some unspecified error occured"
    MissingApiRoute s → printf "missing api route for `%s`" s
    NoCookie          → "No cookie found"
    SomeProtocolError e → displayException e
    SessionInvalid    → "Session invalid, please log in again"
    BadRequest        → "Bad request!"
    LoginFail         → "Login failure"

instance Semigroup ProtocolError where
  a <> _ = a

instance Monoid ProtocolError where
  mempty = UnspecifiedError

instance ToJSON ProtocolError where
  toJSON err = object
    [ "error" .= displayException err
    ]

type MonadProtocol m =
  ( MonadReader Env m
  , Database.HasConnection m
  , MonadIO m
  , Database.MonadDatabaseError m
  , MonadError ProtocolError m
  , MonadSnap m
  )

instance Monad m ⇒ Database.HasConnection (ReaderT Env m) where
  getConnection = asks connection

-- Not all response codes are mapped in `snap`.
data Reason = UnprocessableEntity

displayReason ∷ Reason → C8.ByteString
displayReason = \case
  UnprocessableEntity → "Unprocessable Entity"

data HttpStatus = Code Int | CodeReason Int Reason

instance Num HttpStatus where
  fromInteger = Code . fromInteger
  (+) = undefined
  (*) = undefined
  abs = undefined
  signum = undefined
  negate = undefined

-- Could perhaps pick better error codes.
errResponseCode ∷ ProtocolError → HttpStatus
errResponseCode = \case
  DatabaseError err   → dbErrResponseCode err
  UnspecifiedError    → 500
  MissingApiRoute{}   → 501
  NoCookie            → 400
  SomeProtocolError{} → 400
  SessionInvalid      → 400
  BadRequest          → 400
  LoginFail           → 401

dbErrResponseCode ∷ Database.Error → HttpStatus
dbErrResponseCode = \case
  Database.NoUserFound             → 401
  Database.LangNotFound            → 400
  Database.MultipleUsers           → 401
  Database.NoCurrentSession        → 401
  Database.SessionTimeout          → 401
  Database.MultipleSessions        → 401
  Database.NoExercisesInLesson     → 400
  Database.NonUniqueLesson         → 400
  Database.NotAuthenticated        → 401
  Database.DriverError{}           → 500
  -- Not quite sure what is the right option here.
  Database.UserAlreadyExists       → 422 |> UnprocessableEntity
  where
  (|>) = CodeReason

setResponseCode ∷ HttpStatus → Snap.Response → Snap.Response
setResponseCode s = case s of
  Code n → Snap.setResponseCode n
  CodeReason n r → Snap.setResponseStatus n (displayReason r)

-- | Errors are returned as JSON responses.
runProtocolT :: MonadSnap m ⇒ ToJSON a ⇒ String → ProtocolT m a → m ()
runProtocolT db app = do
  Snap.modifyResponse (Snap.setContentType "application/json")
  conn ← openConnection db
  env  ← throwLeft <$> getEnv conn
  res  ← runExceptT $ flip runReaderT env $ unProtocolT app
  case res of
    Left err → do
       Snap.modifyResponse . setResponseCode . errResponseCode $ err
       Snap.writeLBS $ encode err
    Right resp → Snap.writeLBS $ encode resp

openConnection ∷ MonadIO io ⇒ String → io Connection
openConnection = liftIO . SQL.open

getEnv :: MonadIO io => Connection → io (Either Database.Error Env)
getEnv conn = do
  ctxts ← liftIO $ Database.runDb initContexts conn
  pure $ Env conn <$> ctxts

registerRoutes ∷ String → Snap.Initializer v w ()
registerRoutes db = Snap.addRoutes (apiRoutes db)

-- | Map requests to various handlers.
apiRoutes :: ∀ v w . String → [(B.ByteString, Snap.Handler v w ())]
apiRoutes db =
  [ "login"        |> run loginHandler
  , "logout"       |> run logoutHandler
  , "lessons"      |> run lessonsHandler
  , "lesson"       |> run lessonHandler
  , "menu"         |> run menuHandler
  , "create-user"  |> run createUserHandler
  , "change-pwd"   |> run changePwdHandler
  -- TODO What are these requests?
  , "MOTDRequest"  |> run (missingApiRoute "MOTDRequest")
  , "DataResponse" |> run (missingApiRoute "DataResponse")
  ]
  where
    run ∷ ToJSON a ⇒ ProtocolT (Snap.Handler v w) a → Snap.Handler v w ()
    run = runProtocolT @(Snap.Handler v w) db
    (|>) = (,)

createUserHandler ∷ MonadProtocol m ⇒ m ()
createUserHandler = do
  User{..} ← getMessage
  void $ Database.addUser name password True

-- | Change password of the user.  The user currently (as of this
-- writing) does not need to be authenticated to change their
-- password.  They must simply provide their old password which is
-- then checked against the database.
changePwdHandler ∷ MonadProtocol m ⇒ m ()
changePwdHandler = do
  ChangePwd{..} ← getMessage
  void $ Database.changePassword name oldPassword newPassword

missingApiRoute ∷ MonadError ProtocolError m ⇒ String -> m ()
missingApiRoute = throwError . MissingApiRoute

-- | Reads the data from the request and deserializes from JSON.
getMessage :: FromJSON json ⇒ MonadProtocol m => m json
getMessage = Snap.runRequestBody act
  where
    act stream = do
      s <- fromMaybe errStream <$> Streams.read stream
      let
        errDecode e
          = error
          $ printf "Protocol.getMessage: Error decoding JSON: %s (%s)" e (C8.unpack s)
      case eitherDecode (LBS.fromStrict s) of
        Left e ->  errDecode e
        Right v -> pure v
    errStream = error $ printf "Protocol.getMessage: Error reading request body."

-- TODO Token should be set as an HTTP header.
-- FIXME Use ByteString
-- | Gets the current session token.
getToken :: MonadProtocol m ⇒ m Text
getToken = do
  m <- getTokenCookie
  case m of
    Just c -> pure $ convertString $ Snap.cookieValue c
    Nothing -> throwError NoCookie

getTokenCookie :: MonadProtocol m ⇒ m (Maybe Snap.Cookie)
getTokenCookie = Snap.getCookie "LOGIN_TOKEN"


-- * Handlers
lessonsHandler :: MonadProtocol m ⇒ m ServerMessage
lessonsHandler = do
  t ← getToken
  lessons ← Database.listLessons t
  verifyMessage (SMLessonsList lessons)

lessonHandler :: MonadProtocol m ⇒ m ServerMessage
lessonHandler = Snap.pathArg $ \p → do
  t <- getToken
  handleLessonInit t p

menuHandler :: MonadProtocol m ⇒ m ServerMessage
menuHandler = do
  req <- getMessage
  token <- getToken
  case req of
    (CMMenuRequest lesson score time a b)
      -> handleMenuRequest token lesson score time a b
    _ -> throwError BadRequest

loginHandler :: MonadProtocol m ⇒ m ServerMessage
loginHandler = Snap.method Snap.POST $ do
  (usr, pwd) <- getUser
  handleLoginRequest usr pwd

logoutHandler :: MonadProtocol m ⇒ m ()
logoutHandler
  = Snap.method Snap.POST
  $ getToken >>= handleLogoutRequest

-- TODO Now how this info should be retreived
-- | Returns @(username, password)@.
getUser :: MonadProtocol m ⇒ m (Text, Text)
getUser = (\(CMLoginRequest usr pwd) -> (usr, pwd)) <$> getMessage

setLoginCookie
  :: MonadProtocol m
  => Text -- ^ The token
  -> m ()
setLoginCookie tok = Snap.modifyResponse $ Snap.addResponseCookie c
  where
    c = Snap.Cookie "LOGIN_TOKEN" (T.encodeUtf8 tok)
      Nothing Nothing (pure "/") False False

-- TODO I think we shouldn't be using sessions for this.  I think the
-- way to go is to use the basic http authentication *on every
-- request*.  That is, the client submits user/password on every
-- request.  Security is handled by SSL in the transport layer.
-- Further thought: Well, we're just sending the authentication token
-- in stead.  This one also cannot be spoofed.
handleLoginRequest
  :: MonadProtocol m
  => Text -- ^ Username
  -> Text -- ^ Password
  -> m ServerMessage
handleLoginRequest user pass = do
  Database.authUser user pass
  token ← Database.startSession user
  setLoginCookie token
  pure $ SMLoginSuccess token

askContexts :: MonadProtocol m ⇒ m Contexts
askContexts = asks contexts

handleLessonInit
  ∷ ∀ m
  . MonadProtocol m
  ⇒ Text -- ^ Token
  → Text -- ^ Lesson
  → m ServerMessage
handleLessonInit token lesson = do
    c <- askContexts
    (_sourceLang,sourceTree,_targetLang,targetTree)
      <- Database.startLesson token lesson
    let
      ann ∷ MonadError ProtocolError m ⇒ Unannotated → m Annotated
      ann = annotate c lesson
    src ← ann sourceTree
    trg ← ann targetTree
    let
      (a,b) = assembleMenus c lesson src trg
    verifyMessage (SMMenuList lesson False 0 a b)

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
  ⇒ Text            -- ^ Token
  → Text            -- ^ Lesson
  → Integer         -- ^ Clicks
  → NominalDiffTime -- ^ Time elapsed
  → ClientTree      -- ^ Source tree
  → ClientTree      -- ^ Target tree
  → m ServerMessage
handleMenuRequest token lesson clicks time src trg = do
  c <- askContexts
  verifySession
  finished ← oneSimiliarTree c lesson src trg
  act <-
    if finished
    then do
      Database.finishExercise token lesson time clicks
      pure (\_ _ → emptyMenus)
    else pure assembleMenus
  -- Lift 'unambiguous' into 'IO' to enable throwing (IO) exceptions.
  let ann ∷ ClientTree → m Annotated
      ann = annotate c lesson . Ajax.unClientTree
  srcUnamb ← ann src
  trgUnamb ← ann trg
  let (a , b) = act c lesson srcUnamb trgUnamb
  verifyMessage (SMMenuList lesson finished (succ clicks) a b)

annotate
  ∷ MonadError ProtocolError m
  ⇒ Contexts
  → Text
  → Unannotated
  → m Annotated
annotate cs lesson s = liftEither $ do
  ctxt ← getContext cs lesson $ l
  Unannotated.annotate
    (ErrorCall $ "Unable to parse: " <> show s) ctxt s
  where
  l ∷ Sentence.Language
  l = Sentence.language s

oneSimiliarTree
  ∷ ∀ m
  . MonadError ProtocolError m
  ⇒ Contexts
  → Text
  → ClientTree
  → ClientTree
  → m Bool
oneSimiliarTree cs lesson src trg = do
  srcS ← parse src
  trgS ← parse trg
  pure $ oneInCommon srcS trgS
  where
  oneInCommon ∷ Ord a ⇒ Set a → Set a → Bool
  oneInCommon a b = not $ Set.null $ Set.intersection a b
  parse ∷ ClientTree → m (Set TTree)
  parse = fmap Set.fromList . disambiguate cs lesson

disambiguate
  ∷ ∀ m
  . MonadError ProtocolError m
  ⇒ Contexts
  → Text
  → ClientTree
  → m [TTree]
disambiguate cs lesson t = do
  c ← getC s
  pure $ Sentence.disambiguate c s
    where
    s ∷ Unannotated
    s = Ajax.unClientTree t
    getC ∷ Unannotated → m Context
    getC u = liftEither $ getContext cs lesson (Sentence.language u)

handleLogoutRequest ∷ MonadProtocol m ⇒ Text → m ()
handleLogoutRequest = Database.endSession

-- | @'verifySession' tok@ verifies the user identified by @tok@.
-- This method throws (using one of the error instances of
-- 'MonadProtocol') if the user is not authenticated.
verifySession ∷ MonadProtocol m ⇒ m ()
verifySession = getToken >>= Database.verifySession

-- | Returns the same message unmodified if the user is authenticated,
-- otherwise return 'SMSessionInvalid'.
verifyMessage
  ∷ MonadProtocol m
  ⇒ ServerMessage     -- ^ The message to verify
  → m ServerMessage
verifyMessage msg = msg <$ verifySession

initContexts
  :: Database.MonadDB db
  => db Contexts
initContexts = mkContexts <$> Database.getLessons

mkContexts ∷ [Database.Lesson] → Contexts
mkContexts = Map.fromList . map mkContext

mkContext
  ∷ Database.Lesson
  → (Text, Map.Map Sentence.Language Context)
mkContext Database.Lesson{..}
  = (name, Map.mapKeys f m)
  where
  m ∷ Map Text Context
  m = Muste.langAndContext nfo grammar
  f ∷ Text → Sentence.Language
  f l = Sentence.Language (Sentence.Grammar grammar) l
  nfo ∷ Linearization.BuilderInfo
  nfo = Linearization.BuilderInfo
    { searchDepth = searchLimitDepth
    , searchSize  = searchLimitSize
    }

-- | Gets the menus for a lesson.  This consists of a source tree and
-- a target tree.
assembleMenus
  ∷ Contexts
  → Text
  → Annotated
  → Annotated
  → (ServerTree,ServerTree)
assembleMenus c lesson src trg =
  ( mkTree src
  , mkTree trg
  )
  where
  mkTree = makeTree c lesson

data ProtocolException
  = LessonNotFound Text
  | LanguageNotFound Sentence.Language

deriving instance Show ProtocolException

instance Exception ProtocolException where

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
  = Ajax.serverTree s menu
  where
  menu = Muste.getMenu (mempty @Menu.PruneOpts) ctxt (Sentence.linearization s)
  ctxt = throwLeft $ getContext c lesson language
  language = Sentence.language s

emptyMenus
  ∷ Annotated -- ^ Source sentence
  → Annotated -- ^ Target sentence
  → (ServerTree, ServerTree)
emptyMenus src trg =
  ( mkTree src
  , mkTree trg
  )
  where
  -- FIXME In 'assembleMenus' we actually use the language of the tree
  -- we're building.  Investigate if this may be a bug.  Similiarly
  -- for 'lin'.  This is the reason we are not using 'makeTree' here.
  mkTree ∷ Annotated → ServerTree
  mkTree s
    = Ajax.serverTree (Sentence.sentence language lin) mempty
    where
    lin = Sentence.linearization s
    language = Sentence.language s
