{-# Language RecordWildCards #-}
{-# OPTIONS_GHC -Wall -Wno-orphans #-}
module Protocol
  ( registerRoutes
  ) where

import Data.Aeson
import Data.Map (Map)
import qualified Data.Map.Lazy as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad
import Database.SQLite.Simple
import Control.Monad.Reader
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C8
import Snap (MonadSnap)
import qualified Snap
import qualified System.IO.Streams as Streams
import Text.Printf
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Data.Time
import Data.Function (on, (&))
import Control.Monad.Catch (MonadThrow(throwM))
import Control.Exception
  (Exception, ErrorCall(ErrorCall))
import Control.Category ((>>>))

import Muste (Context, TTree)
import qualified Muste
import qualified Muste.Sentence as Sentence
import Muste.Sentence.Annotated (Annotated)
import Muste.Sentence.Unannotated (Unannotated)
import qualified Muste.Sentence.Unannotated as Unannotated

import Common

import Ajax
  ( ServerMessage(..), ClientMessage(..)
  , ClientTree(..), ServerTree
  )
import qualified Ajax
import Database (MonadDB, getConnection)
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
type ProtocolT m a = ReaderT Env m a

type MonadProtocol m =
  ( MonadReader Env m
  , Database.HasConnection m
  , MonadIO m
  )

instance MonadIO m ⇒ Database.HasConnection (ReaderT Env m) where
  getConnection = asks connection

runProtocolT :: MonadSnap m ⇒ ToJSON a ⇒ String → ProtocolT m a → m ()
runProtocolT db app = do
  Snap.modifyResponse (Snap.setContentType "application/json")
  conn ← liftIO $ open db
  env <- getEnv conn
  res ← app `runReaderT` env
  Snap.writeLBS $ encode res

getEnv :: MonadIO io => Connection → io Env
getEnv conn = do
  ctxts <- liftIO $ Database.runDB initContexts conn
  pure $ Env conn ctxts

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
  -- TODO What are these requests?
  , "MOTDRequest"  |> err "MOTDRequest"
  , "DataResponse" |> err "DataResponse"
  ]
  where
    run = runProtocolT @(Snap.Handler v w) db
    (|>) = (,)
    err :: String -> a
    err = error . printf "missing api route for `%s`"

-- | Reads the data from the request and deserializes from JSON.
getMessage :: FromJSON json ⇒ MonadSnap m ⇒ MonadProtocol m => m json
getMessage = Snap.runRequestBody act
  where
    act stream = do
      s <- fromMaybe errStream <$> Streams.read stream
      case eitherDecode (LBS.fromStrict s) of
        Left e ->  errDecode e
        Right v -> pure v
    errStream = error $ printf "Protocol.getMessage: Error reading request body."
    errDecode = error . printf "Protocol.getMessage: Error decoding JSON: %s"

-- TODO Token should be set as an HTTP header.
-- FIXME Use ByteString
-- | Gets the current session token.
getToken :: MonadSnap m ⇒ MonadProtocol m ⇒ m String
-- getToken = cheatTakeToken <$> getMessage
getToken = do
  m <- getTokenCookie
  case m of
    Just c -> pure $ C8.unpack $ Snap.cookieValue c
    Nothing -> error
      $ printf "Warning, reverting back to deprecated way of handling sesson cookies\n"

getTokenCookie :: MonadSnap m ⇒ MonadProtocol m ⇒ m (Maybe Snap.Cookie)
getTokenCookie = Snap.getCookie "LOGIN_TOKEN"


-- * Handlers
lessonsHandler :: MonadSnap m ⇒ MonadProtocol m ⇒ m ServerMessage
lessonsHandler = do
  token <- getToken
  handleLessonsRequest token

lessonHandler :: MonadSnap m ⇒ MonadProtocol m ⇒ m ServerMessage
lessonHandler = Snap.pathArg $ \p → do
  t <- getToken
  handleLessonInit t p

menuHandler :: MonadSnap m ⇒ MonadProtocol m ⇒ m ServerMessage
menuHandler = do
  req <- getMessage
  token <- getToken
  case req of
    (CMMenuRequest lesson score time a b)
      -> handleMenuRequest token lesson score time a b
    _ -> error "Wrong request"

loginHandler :: MonadSnap m ⇒ MonadProtocol m ⇒ m ServerMessage
loginHandler = Snap.method Snap.POST $ do
  (usr, pwd) <- getUser
  handleLoginRequest usr pwd

logoutHandler :: MonadSnap m ⇒ MonadProtocol m ⇒ m ServerMessage
logoutHandler = Snap.method Snap.POST $ do
  tok <- getToken
  handleLogoutRequest tok

-- TODO Now how this info should be retreived
-- | Returns @(username, password)@.
getUser :: MonadSnap m ⇒ MonadProtocol m ⇒ m (Text, Text)
getUser = (\(CMLoginRequest usr pwd) -> (usr, pwd)) <$> getMessage

setLoginCookie
  :: MonadSnap m
  => MonadProtocol m
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
handleLoginRequest
  :: MonadSnap m
  => MonadProtocol m
  => Text -- ^ Username
  -> Text -- ^ Password
  -> m ServerMessage
handleLoginRequest user pass = do
  authed <- Database.authUser user pass
  token  <- Database.startSession user
  if authed
  then SMLoginSuccess token
    <$ setLoginCookie token
  else pure $ SMLoginFail

askContexts :: MonadProtocol m ⇒ m Contexts
askContexts = asks contexts

handleLessonsRequest :: MonadProtocol m ⇒ String -> m ServerMessage
handleLessonsRequest token = do
  lessons <- Database.listLessons (T.pack token)
  verifyMessage token (SMLessonsList $ Ajax.lessonFromTuple <$> lessons)

handleLessonInit
  ∷ MonadProtocol m
  ⇒ String -- ^ Token
  → Text   -- ^ Lesson
  → m ServerMessage
handleLessonInit token lesson = do
    c <- askContexts
    (sourceLang,sourceTree,targetLang,targetTree)
      <- Database.startLesson token lesson
    let (a,b) = assembleMenus c lesson
                (stce sourceLang sourceTree)
                (stce targetLang targetTree)
    verifyMessage token (SMMenuList lesson False 0 a b)
    where
    stce ∷ Text → Annotated → Annotated
    stce l t = (Sentence.sentence (Sentence.Language g l) (Sentence.linearization t))
    g ∷ Sentence.Grammar
    g = "STUB"

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
  :: MonadProtocol m
  => String          -- ^ Token
  -> Text            -- ^ Lesson
  -> Integer         -- ^ Clicks
  -> NominalDiffTime -- ^ Time elapsed
  -> ClientTree      -- ^ Source tree
  -> ClientTree      -- ^ Target tree
  -> m ServerMessage
handleMenuRequest token lesson clicks time src trg = do
  c <- askContexts
  mErr <- verifySession token
  let authd = not $ isJust mErr
  let finished ∷ Bool
      finished = oneSimiliarTree c lesson src trg
  act <-
    if finished
    then do
      when authd (Database.finishExercise token lesson time clicks)
      pure (\_ _ → emptyMenus)
    else pure assembleMenus
  -- Lift 'unambiguous' into 'IO' to enable throwing (IO) exceptions.
  srcUnamb ← liftIO $ unambiguous c lesson src
  trgUnamb ← liftIO $ unambiguous c lesson trg
  let (a , b) = act c lesson srcUnamb trgUnamb
  verifyMessage token (SMMenuList lesson finished (succ clicks) a b)

unambiguous
  ∷ MonadThrow m
  ⇒ Contexts
  → Text
  → ClientTree
  → m Annotated
unambiguous cs lesson t = Unannotated.unambiguous
    (ErrorCall $ "Unable to parse: " <> show s) ctxt s
  where
  ctxt ∷ Context
  ctxt = fromMaybe err $ getContext cs lesson $ Sentence.language s
  err = error "Context not found for language"
  s ∷ Unannotated
  s = Ajax.unClientTree t

oneSimiliarTree
  ∷ Contexts
  → Text
  → ClientTree
  → ClientTree
  → Bool
oneSimiliarTree cs lesson
  = oneInCommon `on` parse
  where
  oneInCommon ∷ Ord a ⇒ Set a → Set a → Bool
  oneInCommon a b = not $ Set.null $ Set.intersection a b
  parse ∷ ClientTree → Set TTree
  parse t
    = t
    & disambiguate cs lesson
    & Set.fromList

disambiguate ∷ Contexts → Text → ClientTree → [TTree]
disambiguate cs lesson t
  = Sentence.disambiguate (getC s) s
    where
    s ∷ Unannotated
    s = Ajax.unClientTree t
    getC
      =   Sentence.language
      >>> getContext cs lesson
      >>> fromMaybe err
    err = error "Lang not found for tree in grammar"

handleLogoutRequest :: MonadProtocol m ⇒ String -> m ServerMessage
handleLogoutRequest token = do
  Database.endSession token
  pure $ SMLogoutResponse

-- | @'verifySession' tok@ verifies the user identified by
-- @tok@. Returns 'Nothing' if authentication is successfull and @Just
-- err@ if not. @err@ is a message describing what went wrong.
verifySession
  :: MonadProtocol m
  => String -- ^ The token of the logged in user
  -> m (Maybe String)
verifySession tok = Database.verifySession tok

-- | Returns the same message unmodified if the user is authenticated,
-- otherwise return 'SMSessionInvalid'.
verifyMessage
  :: MonadProtocol m
  => String -- ^ The logged in users session id.
  -> ServerMessage     -- ^ The message to verify
  -> m ServerMessage
verifyMessage tok msg = do
  m <- verifySession tok
  pure $ case m of
    Nothing  -> msg
    Just err -> SMSessionInvalid err

initContexts
  :: Database.MonadDB db
  => db Contexts
initContexts = mkContexts <$> Database.getLessons

mkContexts ∷ [Database.Lesson] → Contexts
mkContexts = Map.fromList . map mkContext

mkContext
  ∷ Database.Lesson
  → (Text, Map.Map Sentence.Language Context)
mkContext (ls, _, nm, _, _, _, _, _) =
  (ls, Map.mapKeys (Sentence.Language stub) $ Muste.langAndContext mempty nm)
  where
  stub ∷ Sentence.Grammar
  stub = "STUB"

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
  menu = Muste.getMenu ctxt (Sentence.linearization s)
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
