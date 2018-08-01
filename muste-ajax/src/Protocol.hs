{-# language
    LambdaCase
  , OverloadedStrings
  , TypeApplications
  , ViewPatterns
  , FlexibleContexts
#-}
module Protocol
  ( apiRoutes
  ) where

import Data.Aeson
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map ((!),Map)
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

import Muste (Context, Path, TTree, Linearization)
import qualified Muste

import Ajax
  ( ServerMessage(..), ClientMessage(..)
  , ClientTree(..), ServerTree(..)
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
    wrap act = runProtocol $ act >>= Snap.writeLBS . encode
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
getConnection = Config.getDB >>= open

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
                (sourceLang,pure sourceTree)
                (targetLang,pure targetTree)
    verifyMessage token (SMMenuList lesson False 0 a b)

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
  ctreea@(ClientTree langa srcTrees)
  ctreeb@(ClientTree langb trgTrees) = do
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
                 (langa, srcTrees)
                 (langb, trgTrees)
  verifyMessage token (SMMenuList lesson finished (succ clicks) a b)
  where
    finished :: Bool
    finished = ctreea `same` ctreeb

-- | Two 'ClientTree''s are considered the same if they have just one
-- 'TTree' in common.  This uses the 'Eq' instance for 'TTree' (so
-- that better work).
same :: ClientTree -> ClientTree -> Bool
same = oneSame `on` thetrees
  where
  thetrees :: ClientTree -> Set TTree
  thetrees (ClientTree _ trees) = S.fromList trees
  oneSame :: Set TTree -> Set TTree -> Bool
  oneSame a b = not $ S.null $ S.intersection a b

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
  conn <- askConnection
  m <- verifySession tok
  pure $ case m of
    Nothing  -> msg
    Just err -> SMSessionInvalid err

initContexts
  :: MonadIO io
  => Connection
  -> io Contexts
initContexts conn = liftIO $ do
  lessonGrammarList <- Database.getLessons conn
  M.fromList <$> (mapM mkContext lessonGrammarList)

mkContext :: Database.Lesson -> IO (Text, M.Map String Context)
mkContext (ls, _, nm, _, _, _, _, _) = do
  langs <- Muste.langAndContext (T.unpack nm)
  pure (ls, M.fromList langs)

-- FIXME At the moment the menu is not really a list of menus but
-- instead a list with only one menu as the only element
-- | Gets the menus for a lesson, two trees and two languages
assembleMenus
  :: Contexts
  -> Text
  -> (String, [TTree]) -- ^ Source language and tree
  -> (String, [TTree]) -- ^ Target language and tree
  -> (ServerTree,ServerTree)
assembleMenus contexts lesson src@(srcLang, srcTree) trg@(_, trgTree) =
  ( mkTree src
  , mkTree trg
  )
  where
  mkTree = makeTree contexts lesson src trg

-- We could make the constraint on `m` more general, but then I get
-- into some stuff with some functional dependencies that I'm not
-- entirely sure how works.
getContext
  :: Text -- ^ The lesson
  -> String -- ^ The language
  -> Protocol v w Context
getContext lesson lang = do
  ctxts <- askContexts
  pure $ ctxts ! lesson ! lang

-- | @'makeTree' ctxt lesson src trg tree@ Creates a 'ServerTree' from
-- a source trees and a target tree.  The 'Menu' is provided given
-- @tree@.
makeTree
  :: Contexts -> Text
  -> (String, [TTree])
  -> (String, [TTree])
  -> (String, [TTree])
  -> ServerTree
makeTree contexts lesson (srcLang, srcTrees) (trgLang, trgTrees) (lang, trees)
  = Ajax.mkServerTree lang trees lin (Muste.getCleanMenu ctxt tree)
    where
    grammar = Muste.ctxtGrammar (contexts ! lesson ! srcLang)
    ctxt    = contexts ! lesson ! lang
    lin     = Muste.mkLin ctxt srcTree trgTree tree
    srcTree = unsafeTakeTree srcTrees
    trgTree = unsafeTakeTree trgTrees
    tree    = unsafeTakeTree trees

emptyMenus
  :: Contexts
  -> Text
  -> (String, [TTree]) -- ^ Source language and tree
  -> (String, [TTree]) -- ^ Target language and tree
  -> (ServerTree, ServerTree)
emptyMenus contexts lesson src@(srcLang, srcTrees) trg@(_, trgTrees) =
  ( mkTree src
  , mkTree trg
  )
  where
  -- FIXME In 'assembleMenus' we actually use the language of the tree
  -- we're building.  Investigate if this may be a bug.  Similiarly
  -- for 'lin'.  This is the reason we are not using 'makeTree' here.
  ctxt = contexts ! lesson ! srcLang
  grammar = Muste.ctxtGrammar ctxt
  srcTree = unsafeTakeTree srcTrees
  trgTree = unsafeTakeTree trgTrees
  lin = Muste.mkLin ctxt srcTree trgTree
  mkTree (lang, trees) = Ajax.mkServerTree
    lang trees (lin tree) mempty
    where
    tree = unsafeTakeTree trees

-- TODO Both unsafe and a dirty hack!
unsafeTakeTree :: [TTree] -> TTree
unsafeTakeTree = fromMaybe err . listToMaybe
  where
  err = error "Protocol.unsafeTakeTree: A hack shows its true colors."
