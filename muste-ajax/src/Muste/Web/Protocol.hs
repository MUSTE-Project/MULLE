{-# Language RecordWildCards, UndecidableInstances, DeriveAnyClass #-}
{-# OPTIONS_GHC -Wall -Wcompat #-}
module Muste.Web.Protocol
  ( apiInit
  , AppState
  ) where

import Prelude ()
import Muste.Prelude
import Muste.Prelude.Extra
import Muste.Prelude.SQL (Connection)
import qualified Muste.Prelude.SQL as SQL

import Data.Aeson
import Data.Map (Map)
import qualified Data.Map.Lazy as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Reader
import Data.ByteString (ByteString)
import Snap (MonadSnap)
import qualified Snap
import qualified System.IO.Streams as Streams
import Control.Monad.Trans.Control (MonadBaseControl)
import Control.Monad.Base (MonadBase)
import qualified Snap.Util.CORS as Cors

import           Muste (Context, TTree)
import qualified Muste
import qualified Muste.Sentence as Sentence
import           Muste.Sentence.Annotated (Annotated)
import           Muste.Sentence.Unannotated (Unannotated)
import qualified Muste.Sentence.Unannotated as Unannotated
import qualified Muste.Menu as Menu
import qualified Muste.Linearization as Linearization

import           Muste.Web.Ajax (ClientTree, ServerTree)
import qualified Muste.Web.Ajax            as Ajax
import           Muste.Web.Database (MonadDB, MonadDatabaseError(..))
import qualified Muste.Web.Database        as Database
import qualified Muste.Web.Database.Types  as Database
import           Muste.Web.Types.Score (Score(Score))
import qualified Muste.Web.Types.Score     as Score

-- | Maps a lesson to a map from grammars(-identifiers) to their
-- corresponding contexts.
type Contexts = Map Text (Map Sentence.Language Context)

-- | The state that the server will have throughout the uptime.
data AppState = AppState
  { connection    ∷ Connection
  , contexts      ∷ Contexts
  , knownGrammars ∷ Muste.KnownGrammars
  }

instance Muste.HasKnownGrammars AppState where
  giveKnownGrammars = knownGrammars

-- | A simple monad transformer for handling responding to requests.
newtype ProtocolT m a = ProtocolT
  { unProtocolT ∷ ExceptT ProtocolError m a
  }

deriving newtype instance Functor m      ⇒ Functor      (ProtocolT m)
deriving newtype instance Monad m        ⇒ Applicative  (ProtocolT m)
deriving newtype instance Monad m        ⇒ Monad        (ProtocolT m)
deriving newtype instance MonadIO m      ⇒ MonadIO      (ProtocolT m)
deriving newtype instance MonadBaseControl IO m ⇒ MonadBaseControl IO (ProtocolT m)
deriving newtype instance MonadBase IO m ⇒ MonadBase IO (ProtocolT m)
deriving newtype instance MonadReader AppState m ⇒ MonadReader AppState (ProtocolT m)
deriving newtype instance MonadPlus m    ⇒ MonadPlus    (ProtocolT m)
deriving newtype instance Monad m        ⇒ Alternative  (ProtocolT m)
deriving newtype instance MonadSnap m    ⇒ MonadSnap    (ProtocolT m)
deriving newtype instance Monad m        ⇒ MonadError ProtocolError (ProtocolT m)
deriving newtype instance Muste.MonadGrammar m ⇒ Muste.MonadGrammar (ProtocolT m)

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
  | NoAccessToken
  | BadRequest
  | SessionInvalid
  | LoginFail
  | ErrReadBody
  | DecodeError String
  | LessonNotFound Text
  | LanguageNotFound Sentence.Language

deriving stock instance Show ProtocolError

instance Exception ProtocolError where
  displayException = \case
    DatabaseError err   → "A database error occurred: " <> displayException err
    UnspecifiedError    → "Some unspecified error occured"
    MissingApiRoute s   → printf "missing api route for `%s`" s
    NoAccessToken       → "No cookie found"
    SomeProtocolError e → displayException e
    SessionInvalid      → "Session invalid, please log in again"
    BadRequest          → "Bad request!"
    LoginFail           → "Login failure"
    ErrReadBody         → "Error reading request body."
    DecodeError s       → printf "Error decoding JSON: %s" s
    LessonNotFound l    → printf "Lesson now found %s" (convertString @_ @String l)
    LanguageNotFound l  → printf "Language not found %s" (show l)

instance Semigroup ProtocolError where
  a <> _ = a

instance Monoid ProtocolError where
  mempty = UnspecifiedError

-- There might be better ways of handling this I suppose...  Another
-- idea would be to generate a tree (since errors can be nested).
-- | Application specific unique error code for responses.
errorIdentifier ∷ ProtocolError → Int
errorIdentifier = \case
  DatabaseError err → case err of
    Database.NoUserFound          → 0
    Database.LangNotFound        → 1
    Database.MultipleUsers       → 2
    Database.NoCurrentSession    → 3
    Database.SessionTimeout      → 4
    Database.MultipleSessions    → 5
    Database.NoExercisesInLesson → 6
    Database.NonUniqueLesson     → 7
    Database.NotAuthenticated    → 8
    Database.DriverError{}       → 9
    Database.UserAlreadyExists   → 10
  UnspecifiedError                → 11
  MissingApiRoute{}               → 12
  NoAccessToken                   → 13
  SomeProtocolError{}             → 14
  SessionInvalid                  → 15
  BadRequest                      → 16
  LoginFail                       → 17
  ErrReadBody                     → 18
  DecodeError{}                   → 19
  LessonNotFound{}                → 20
  LanguageNotFound{}              → 21

instance ToJSON ProtocolError where
  toJSON err = object
    [ "error" .= object
      [ "message" .= displayException err
      , "id"      .= errorIdentifier err
      ]
    ]

type MonadProtocol m =
  ( MonadReader AppState m
  , MonadIO m
  , Database.MonadDatabaseError m
  , MonadError ProtocolError m
  , MonadSnap m
  , Muste.MonadGrammar m
  )

instance Database.HasConnection AppState where
  giveConnection = connection

-- Not all response codes are mapped in `snap`.
data Reason = UnprocessableEntity

displayReason ∷ Reason → ByteString
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
  NoAccessToken       → 401
  SomeProtocolError{} → 400
  SessionInvalid      → 400
  BadRequest          → 400
  LoginFail           → 401
  ErrReadBody         → 400
  DecodeError{}       → 400
  LessonNotFound{}    → 400
  LanguageNotFound{}  → 400

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
  Database.UserAlreadyExists       → 400

setResponseCode ∷ HttpStatus → Snap.Response → Snap.Response
setResponseCode s = case s of
  Code n → Snap.setResponseCode n
  CodeReason n r → Snap.setResponseStatus n (displayReason r)

data Response a = Response
  { body   ∷ a
  , status ∷ Maybe HttpStatus
  }

instance Functor Response where
  fmap f (Response b s) = Response (f b) s

instance Applicative Response where
  Response f0 b0 <*> Response a1 b1 = Response (f0 a1) (b0 *> b1)
  pure a = Response a Nothing

instance Semigroup a ⇒ Semigroup (Response a) where
  Response a0 b0 <> Response a1 b1 = Response (a0 <> a1) (b0 *> b1)

instance Monoid a ⇒ Monoid (Response a) where
  mempty = Response mempty Nothing

-- | Errors are returned as JSON responses.
runProtocolT :: MonadSnap m ⇒ ToJSON a ⇒ ProtocolT m (Response a) → m ()
runProtocolT app = do
  Snap.modifyResponse (Snap.setContentType "application/json")
  res  ← runExceptT $ unProtocolT app
  case res of
    Left err → do
       Snap.modifyResponse . setResponseCode . errResponseCode $ err
       Snap.writeLBS $ encode err
    Right resp → respond resp

respond ∷ MonadSnap m ⇒ ToJSON a ⇒ Response a → m ()
respond Response{..} = Snap.writeLBS $ encode body

openConnection ∷ MonadIO io ⇒ String → io Connection
openConnection = liftIO . SQL.open

initApp
  ∷ MonadIO io
  ⇒ String
  → io AppState
initApp db = do
  liftIO $ putStrLn "Initializing app..."
  conn ← openConnection db
  ctxts ← initContexts'' conn
  knownGs ← Muste.noGrammars
  liftIO $ putStrLn "Initializing app... Done"
  pure $ AppState conn ctxts knownGs

initContexts'' ∷ MonadIO io ⇒ Connection → io Contexts
initContexts'' c = Muste.runGrammarT (initContexts' c)

initContexts' ∷ Muste.MonadGrammar m ⇒ Connection → m Contexts
initContexts' conn = do
  Database.runDbT initContexts conn >>= \case
    Left e → liftIO $ throw e
    Right a → pure a

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
  [ "login"        |> loginHandler
  , "logout"       |> logoutHandler
  , "lessons"      |> lessonsHandler
  , "lesson"       |> lessonHandler
  , "menu"         |> menuHandler
  , "create-user"  |> createUserHandler
  , "change-pwd"   |> changePwdHandler
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

-- | Reads the data from the request and deserializes from JSON.
getMessage ∷ ∀ json m . FromJSON json ⇒ MonadProtocol m => m json
getMessage = do
  s ← Snap.runRequestBody Streams.read >>= \case
    Nothing → throwError ErrReadBody
    Just a → pure $ convertString a
  case eitherDecode @json s of
    Left e  → throwError $ DecodeError e
    Right a → pure a

-- TODO Token should be set as an HTTP header.
-- | Gets the current session token.
getToken :: MonadProtocol m ⇒ m Text
getToken = do
  m <- getTokenCookie
  case m of
    Just c -> pure $ convertString $ Snap.cookieValue c
    Nothing -> throwError NoAccessToken

getTokenCookie :: MonadProtocol m ⇒ m (Maybe Snap.Cookie)
getTokenCookie = Snap.getCookie "LOGIN_TOKEN"


-- * Handlers
lessonsHandler :: MonadProtocol m ⇒ m (Response Ajax.LessonList)
lessonsHandler = do
  t ← getToken
  lessons ← Database.getActiveLessons t
  pure <$> verifyMessage (Ajax.LessonList lessons)

lessonHandler ∷ MonadProtocol m ⇒ m (Response Ajax.MenuResponse)
lessonHandler = pure <$> Snap.pathArg handleLessonInit

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
  ⇒ Text -- ^ Lesson
  → m Ajax.MenuResponse
handleLessonInit lesson = do
  token ← getToken
  (_sourceLang,sourceTree,_targetLang,targetTree)
    <- Database.startLesson token lesson
  menu ← assembleMenus lesson sourceTree targetTree
  verifyMessage $ Ajax.MenuResponse
    { lesson = lesson
    , score = mempty
    , menu = menu
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
  menu ←
    if finished
    then do
      Database.finishExercise token lesson newScore
      pure Nothing
    else assembleMenus lesson (un src) (un trg)
  verifyMessage $ Ajax.MenuResponse
    { lesson = lesson
    , score  = newScore
    , menu   = menu
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

initContexts
  ∷ MonadDB r m
  ⇒ Muste.MonadGrammar m
  ⇒ m Contexts
initContexts = do
  lessons ← Database.getLessons
  mkContexts lessons

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

-- | Gets the menus for a lesson.  This consists of a source tree and
-- a target tree.
assembleMenus
  ∷ MonadProtocol m
  ⇒ Text
  → Unannotated
  → Unannotated
  → m (Maybe Ajax.MenuList)
assembleMenus lesson sourceTree targetTree = do
  c ← askContexts
  let mkTree = makeTree c lesson
  let ann = annotate lesson
  src ← ann sourceTree
  trg ← ann targetTree
  pure $ Just $ Ajax.MenuList
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
