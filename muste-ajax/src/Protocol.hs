{-# language LambdaCase, OverloadedStrings, TypeApplications #-}
module Protocol
  ( apiRoutes
  ) where

import Data.Aeson
import Data.Map ((!),Map)
import qualified Data.Map.Lazy as M
import Control.Monad
import Database.SQLite.Simple
import Control.Monad.Reader
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString as B
import qualified Snap
import qualified System.IO.Streams as Streams
import Text.Printf
import Data.Maybe

import Muste

import Ajax
import qualified Database

-- FIXME Do not import this
import qualified Config

type Contexts = Map String (Map String Context)

-- | The data needed for responding to requests.
data Env = Env
  { connection :: Connection
  , contexts   :: Contexts
  }

-- | A simple monad for handling responding to requests.
type App a = ReaderT Env IO a

-- | Map requests to various handlers.
apiRoutes :: [(B.ByteString, Snap.Handler v w ())]
apiRoutes =
  [ "login"        |> wrap (Snap.method Snap.POST loginHandler)
  , "logout"       |> wrap (Snap.method Snap.POST logoutHandler)
  , "lessons"      |> wrap lessonsHandler
  , "lesson"       |> wrap lessonHandler
  , "menu"         |> wrap menuHandler
  -- TODO What are these requests?
  , "MOTDRequest"  |> err "MOTDRequest"
  , "DataResponse" |> err "DataResponse"
  ]
  where
    wrap :: ToJSON a => Snap.Handler v w a -> Snap.Handler v w ()
    wrap act = act >>= Snap.writeLBS . encode
    (|>) = (,)
    err :: String -> a
    err = error . printf "missing api route for `%s`"

-- | Reads the data from the request and deserializes from JSON.
getMessage :: FromJSON json => Snap.Handler v w json
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
-- | Gets the current session token.
getToken :: Snap.Handler v w String
getToken = cheatTakeToken <$> getMessage

-- TODO Set token as HTTP header do not transport token in the JSON.
cheatTakeToken :: ClientMessage -> String
cheatTakeToken = \case
  CMLessonsRequest t -> t
  CMLessonInit t _ -> t
  _ -> error $ printf "Protocol.cheatTakeToken: Token not found in request"


-- * Handlers
lessonsHandler :: Snap.Handler b w ServerMessage
lessonsHandler = do
  token <- getToken
  appToHandler $ handleLessonsRequest token

lessonHandler :: Snap.Handler b w ServerMessage
lessonHandler = do
  -- token <- getToken
  -- lesson <- getLesson
  (CMLessonInit t l) <- getMessage
  appToHandler $ handleLessonInit t l

menuHandler :: Snap.Handler v w ServerMessage
menuHandler = do
  -- liftIO $ printf "Menu handler\n"
  -- traceShowId <$> Snap.readRequestBody 0
  req <- getMessage
  case req of
    (CMMenuRequest token lesson score time a b)
      -> appToHandler $ handleMenuRequest token lesson score time a b
    _ -> error "Wrong request"

loginHandler :: Snap.Handler v w ServerMessage
loginHandler = do
  (usr, pwd) <- getUser
  appToHandler $ handleLoginRequest usr pwd

logoutHandler :: Snap.Handler v w ServerMessage
logoutHandler = do
  req <- getMessage
  case req of
    (CMLogoutRequest usr) -> appToHandler $ handleLogoutRequest usr
    _ -> error "Malformed request"

-- | Returns @(username, password)@.
getUser :: Snap.Handler v w (String, String)
getUser = (\(CMLoginRequest usr pwd) -> (usr, pwd)) <$> getMessage

getConnection :: IO Connection
getConnection = Config.getDB >>= open

getEnv :: Snap.Handler v w Env
getEnv = liftIO $ do
  conn <- getConnection
  ctxts <- Database.initContexts conn
  pure $ Env conn ctxts

appToHandler :: App a -> Snap.Handler v w a
appToHandler app = do
  env <- getEnv
  liftIO $ app `runReaderT` env

handleLoginRequest
  :: String -- ^ Username
  -> String -- ^ Password
  -> App ServerMessage
handleLoginRequest user pass = do
  c <- askConnection
  authed <- lift $ Database.authUser c user pass
  token  <- lift $ Database.startSession c user
  pure $
    if authed
    then SMLoginSuccess token
    else SMLoginFail

askConnection :: App Connection
askConnection = asks connection

askContexts :: App Contexts
askContexts = asks contexts

handleLessonsRequest :: String -> App ServerMessage
handleLessonsRequest token =
  do
    conn <- askConnection
    lessons <- lift $ Database.listLessons conn token
    let lessonList = map (\(name,description,exercises,passedcount,score,time,passed,enabled) -> Lesson name description exercises passedcount score time passed enabled) lessons
    verifyMessage token (SMLessonsList lessonList)

handleLessonInit
  :: String
  -> String
  -> App ServerMessage
handleLessonInit token lesson =
  do
    contexts <- askContexts
    conn <- askConnection
    (sourceLang,sourceTree,targetLang,targetTree) <- lift $ Database.startLesson conn token lesson
    let (a,b) = assembleMenus contexts lesson (sourceLang,sourceTree) (targetLang,targetTree)
    verifyMessage token (SMMenuList lesson False 0 a b )

handleMenuRequest
  :: String
  -> String
  -> Int
  -> Int
  -> ClientTree
  -> ClientTree
  -> App ServerMessage
handleMenuRequest token lesson clicks time ctreea@(ClientTree langa treea) ctreeb@(ClientTree langb treeb) = do
  contexts <- askContexts
  conn <- askConnection
  mErr <- verifySession token
  let authd = not $ isJust mErr
  act <- if finished
  then do
    when authd (lift $ Database.finishExercise conn token lesson time clicks)
    pure emptyMenus
  else pure assembleMenus
  let (a , b) = act contexts lesson (langa , treea) (langb , treeb)
  verifyMessage token (SMMenuList lesson finished (clicks + 1) a b)
  where
    finished :: Bool
    finished = treea == treeb

handleLogoutRequest :: String -> App ServerMessage
handleLogoutRequest token = do
  conn <- askConnection
  lift $ Database.endSession conn token
  pure $ SMLogoutResponse

-- | @'verifySession' tok@ verifies the user identified by
-- @tok@. Returns 'Nothing' if authentication is successfull and @Just
-- err@ if not. @err@ is a message describing what went wrong.
verifySession
  :: String -- ^ The token of the logged in user
  -> App (Maybe String)
verifySession tok = do
  conn <- askConnection
  (authd , err) <- liftIO $ Database.verifySession conn tok
  pure $ if authd
    then Nothing
    else Just err

-- | Returns the same message unmodified if the user is authenticated,
-- otherwise return 'SMSessionInvalid'.
verifyMessage
  :: String -- ^ The logged in users session id.
  -> ServerMessage     -- ^ The message to verify
  -> App ServerMessage
verifyMessage tok msg = do
  conn <- askConnection
  m <- verifySession tok
  pure $ case m of
    Nothing  -> msg
    Just err -> SMSessionInvalid err

-- | Checks if a linearization token matches in both trees
matched :: Path -> TTree -> TTree -> Path
matched p t1 t2 = if selectNode t1 p == selectNode t2 p then p else []

-- FIXME At the moment the menu is not really a list of menus but
-- instead a list with only one menu as the only element
-- | Gets the menus for a lesson, two trees and two languages
assembleMenus :: Map String (Map String Context) -> String -> (String,String) -> (String,String) -> (ServerTree,ServerTree)
assembleMenus contexts lesson src@(srcLang, srcTree) trg@(_, trgTree) =
  ( mkTree src
  , mkTree trg
  )
  where
  grammar = ctxtGrammar (contexts ! lesson ! srcLang)
  parse = parseTTree grammar
  getContext lang = contexts ! lesson ! lang
  match (LinToken path lin _) = LinToken path lin (matched path (parse srcTree) (parse trgTree))
  mkTree (lang, tree) = ServerTree lang tree lin (Menu $ getCleanMenu ctxt (parse tree))
    where
    ctxt = getContext lang
    lin = match <$> linearizeTree ctxt (parseTTree grammar tree)

emptyMenus
  :: Map String (Map String Context)
  -> String
  -> (String, String)
  -> (String, String)
  -> (ServerTree, ServerTree)
emptyMenus contexts lesson src@(srcLang, srcTree) trg@(_, trgTree) =
  ( mkTree src
  , mkTree trg
  )
  where
  -- FIXME In 'assembleMenus' we actually use the language of the tree
  -- we're building.  Investigate if this may be a bug.  Similiarly
  -- for 'lin'.
  ctxt = contexts ! lesson ! srcLang
  grammar = ctxtGrammar ctxt
  parse = parseTTree grammar
  linTree = linearizeTree ctxt
  match (LinToken path lin _) = LinToken path lin (matched path (parse srcTree) (parse trgTree))
  lin t = match <$> linTree (parse t)
  mkTree (lang, tree) = ServerTree lang tree (lin tree) mempty
