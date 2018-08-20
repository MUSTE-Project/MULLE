{-# OPTIONS_GHC -Wno-orphans #-}
{-# language
    LambdaCase
  , OverloadedStrings
  , TypeApplications
  , ViewPatterns
  , FlexibleContexts
  , StandaloneDeriving
  , TupleSections
  , UnicodeSyntax
#-}
module Protocol
  ( apiRoutes
  ) where

import Data.Aeson
import Data.Map (Map)
import qualified Data.Map.Lazy as M
import Control.Monad
import Database.SQLite.Simple
import Control.Monad.Reader
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C8
import qualified Snap
import qualified System.IO.Streams as Streams
import Text.Printf
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Data.Time
import Data.Function (on)
import Control.Monad.Catch (MonadThrow(throwM))
import Control.Exception (Exception, throw)

import Muste (Context, Linearization)
import qualified Muste

import Ajax
  ( ServerMessage(..), ClientMessage(..)
  , ClientTree(..), ServerTree
  )
import qualified Ajax
import qualified Database
import qualified Database.Types as Database

-- FIXME Do not import this
import qualified Config

type Contexts = Map Text (Map String Context)

-- | The data needed for responding to requests.
data Env = Env
  { connection :: Connection
  , contexts   :: Contexts
  }

-- | A simple monad for handling responding to requests.
type Protocol v w a = ReaderT Env (Snap.Handler v w) a

-- Orphan instance!!
instance MonadThrow (Snap.Handler v w) where
  throwM = liftIO . throwM

runProtocol :: Protocol v w a -> Snap.Handler v w a
runProtocol app = do
  env <- getEnv
  app `runReaderT` env

getEnv :: MonadIO m => m Env
getEnv = liftIO $ do
  conn <- getConnection
  ctxts <- initContexts conn
  pure $ Env conn ctxts

-- | Map requests to various handlers.
apiRoutes :: [(B.ByteString, Snap.Handler v w ())]
apiRoutes =
  [ "login"        |> wrap (Snap.method Snap.POST loginHandler)
  , "logout"       |> wrap (Snap.method Snap.POST logoutHandler)
  , "lessons"      |> wrap lessonsHandler
  , "lesson"       |> wrap (Snap.pathArg lessonHandler)
  , "menu"         |> wrap menuHandler
  -- TODO What are these requests?
  , "MOTDRequest"  |> err "MOTDRequest"
  , "DataResponse" |> err "DataResponse"
  ]
  where
    wrap :: ToJSON a => Protocol v w a -> Snap.Handler v w ()
    wrap act = do
        Snap.modifyResponse (Snap.setContentType "application/json")
        runProtocol $ act >>= Snap.writeLBS . encode
    (|>) = (,)
    err :: String -> a
    err = error . printf "missing api route for `%s`"

-- | Reads the data from the request and deserializes from JSON.
getMessage :: FromJSON json => Protocol v w json
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
getToken :: Protocol v w String
-- getToken = cheatTakeToken <$> getMessage
getToken = do
  m <- getTokenCookie
  case m of
    Just c -> pure $ C8.unpack $ Snap.cookieValue c
    Nothing -> error
      $ printf "Warning, reverting back to deprecated way of handling sesson cookies\n"

getTokenCookie :: Protocol v w (Maybe Snap.Cookie)
getTokenCookie = Snap.getCookie "LOGIN_TOKEN"


-- * Handlers
lessonsHandler :: Protocol v w ServerMessage
lessonsHandler = do
  token <- getToken
  handleLessonsRequest token

lessonHandler :: Text -> Protocol v w ServerMessage
lessonHandler p = do
  t <- getToken
  handleLessonInit t p

menuHandler :: Protocol v w ServerMessage
menuHandler = do
  req <- getMessage
  token <- getToken
  case req of
    (CMMenuRequest lesson score time a b)
      -> handleMenuRequest token lesson score time a b
    _ -> error "Wrong request"

loginHandler :: Protocol v w ServerMessage
loginHandler = do
  (usr, pwd) <- getUser
  handleLoginRequest usr pwd

logoutHandler :: Protocol v w ServerMessage
logoutHandler = do
  tok <- getToken
  handleLogoutRequest tok

-- TODO Now how this info should be retreived
-- | Returns @(username, password)@.
getUser :: Protocol v w (Text, Text)
getUser = (\(CMLoginRequest usr pwd) -> (usr, pwd)) <$> getMessage

getConnection :: IO Connection
getConnection = open Config.db

setLoginCookie
  :: Text -- ^ The token
  -> Protocol v w ()
setLoginCookie tok = Snap.modifyResponse $ Snap.addResponseCookie c
  where
    c = Snap.Cookie "LOGIN_TOKEN" (T.encodeUtf8 tok)
      Nothing Nothing (pure "/") False False

-- TODO I think we shouldn't be using sessions for this.  I think the
-- way to go is to use the basic http authentication *on every
-- request*.  That is, the client submits user/password on every
-- request.  Security is handled by SSl in the transport layer.
handleLoginRequest
  :: Text -- ^ Username
  -> Text -- ^ Password
  -> Protocol v w ServerMessage
handleLoginRequest user pass = do
  c <- askConnection
  authed <- liftIO $ Database.authUser c user pass
  token  <- liftIO $ Database.startSession c user
  if authed
  then SMLoginSuccess token
    <$ setLoginCookie token
  else pure $ SMLoginFail

askConnection :: Protocol v w Connection
askConnection = asks connection

askContexts :: Protocol v w Contexts
askContexts = asks contexts

handleLessonsRequest :: String -> Protocol v w ServerMessage
handleLessonsRequest token = do
  conn <- askConnection
  lessons <- liftIO $ Database.listLessons conn (T.pack token)
  verifyMessage token (SMLessonsList $ Ajax.lessonFromTuple <$> lessons)

handleLessonInit
  :: String -- ^ Token
  -> Text -- ^ Lesson
  -> Protocol v w ServerMessage
handleLessonInit token lesson = do
    contexts <- askContexts
    conn <- askConnection
    (sourceLang,sourceTree,targetLang,targetTree)
      <- Database.startLesson conn token lesson
    let (a,b) = assembleMenus contexts lesson
                (sourceLang,sourceTree)
                (targetLang,targetTree)
    verifyMessage token (SMMenuList lesson False 0 a b)

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
  :: String -- ^ Token
  -> Text -- ^ Lesson
  -> Integer -- ^ Clicks
  -> NominalDiffTime -- ^ Time elapsed
  -> ClientTree -- ^ Source tree
  -> ClientTree -- ^ Target tree
  -> Protocol v w ServerMessage
handleMenuRequest
  token lesson clicks time
  ctreea@(ClientTree srcLang srcLin)
  ctreeb@(ClientTree trgLang trgLin) = do
  contexts <- askContexts
  conn <- askConnection
  mErr <- verifySession token
  let authd = not $ isJust mErr
  act <-
    if finished
    then do
      when authd (liftIO $ Database.finishExercise conn token lesson time clicks)
      pure emptyMenus
    else pure assembleMenus
  let (a , b) = act contexts lesson
                 (srcLang, srcLin)
                 (trgLang, trgLin)
  verifyMessage token (SMMenuList lesson finished (succ clicks) a b)
  where
    finished :: Bool
    finished = ctreea `sameLin` ctreeb

-- | Checks if two Two 'ClientTree''s have the same linearization.
sameLin :: ClientTree -> ClientTree -> Bool
sameLin = (==)
  `on` thetrees
  where
  thetrees :: ClientTree -> Linearization
  thetrees (ClientTree _ trees) = trees

handleLogoutRequest :: String -> Protocol v w ServerMessage
handleLogoutRequest token = do
  conn <- askConnection
  liftIO $ Database.endSession conn token
  pure $ SMLogoutResponse

-- | @'verifySession' tok@ verifies the user identified by
-- @tok@. Returns 'Nothing' if authentication is successfull and @Just
-- err@ if not. @err@ is a message describing what went wrong.
verifySession
  :: String -- ^ The token of the logged in user
  -> Protocol v w (Maybe String)
verifySession tok = do
  conn <- askConnection
  liftIO $ Database.verifySession conn tok

-- | Returns the same message unmodified if the user is authenticated,
-- otherwise return 'SMSessionInvalid'.
verifyMessage
  :: String -- ^ The logged in users session id.
  -> ServerMessage     -- ^ The message to verify
  -> Protocol v w ServerMessage
verifyMessage tok msg = do
  m <- verifySession tok
  pure $ case m of
    Nothing  -> msg
    Just err -> SMSessionInvalid err

initContexts
  :: MonadIO io
  => Connection
  -> io Contexts
initContexts conn = liftIO $ mkContexts <$> Database.getLessons conn

mkContexts ∷ [Database.Lesson] → Contexts
mkContexts = M.fromList . map mkContext

mkContext :: Database.Lesson -> (Text, M.Map String Context)
mkContext (ls, _, nm, _, _, _, _, _) =
  (ls, Muste.langAndContext (T.unpack nm))

-- | Gets the menus for a lesson.  This consists of a source tree and
-- a target tree.
assembleMenus
  :: Contexts
  -> Text
  -> (String, Linearization) -- ^ Source language and tree
  -> (String, Linearization) -- ^ Target language and tree
  -> (ServerTree,ServerTree)
assembleMenus contexts lesson src trg =
  ( mkTree src
  , mkTree trg
  )
  where
  mkTree = makeTree contexts lesson src trg

data ProtocolException
  = LessonNotFound Text
  | LanguageNotFound String

deriving instance Show ProtocolException

instance Exception ProtocolException where

getContext
  :: MonadThrow m
  => Contexts
  -> Text   -- ^ Lesson
  -> String -- ^ Language
  -> m Context
getContext ctxts lesson lang
  =   pure ctxts
  >>= lookupM (LessonNotFound lesson) lesson
  >>= lookupM (LanguageNotFound lang) lang

lookupM
  :: MonadThrow m
  => Exception e
  => Ord k
  => e -> k -> Map k a -> m a
lookupM err k = liftMaybe err . M.lookup k

-- | Lift a 'Maybe' to any 'MonadThrow'.
liftMaybe :: MonadThrow m => Exception e => e -> Maybe a -> m a
liftMaybe e = \case
  Nothing -> throwM e
  Just a  -> pure a

-- | @'makeTree' ctxt lesson src trg tree@ Creates a 'ServerTree' from
-- a source trees and a target tree.  The 'Menu' is provided given
-- @tree@.
makeTree
  :: Contexts -> Text
  -> (String, Linearization)
  -> (String, Linearization)
  -> (String, Linearization)
  -> ServerTree
makeTree contexts lesson _ _ (lang, trees)
  = Ajax.mkServerTree lang trees (Muste.getMenu ctxt trees)
    where
    ctxt    = throwLeft $ getContext contexts lesson lang

-- | Throws an exception if the it's a 'Left' (requires the left to be
-- an exception).  This method is *unsafe*!
throwLeft :: Exception e => Either e c -> c
throwLeft = either throw id

emptyMenus
  :: Contexts
  -> Text
  -> (String, Linearization) -- ^ Source language and tree
  -> (String, Linearization) -- ^ Target language and tree
  -> (ServerTree, ServerTree)
emptyMenus _ _ src trg =
  ( mkTree src
  , mkTree trg
  )
  where
  -- FIXME In 'assembleMenus' we actually use the language of the tree
  -- we're building.  Investigate if this may be a bug.  Similiarly
  -- for 'lin'.  This is the reason we are not using 'makeTree' here.
  mkTree ∷ (String, Linearization) → ServerTree
  mkTree (lang, trees) = Ajax.mkServerTree lang trees mempty
