{-# language
    LambdaCase
  , OverloadedStrings
  , TypeApplications
  , ViewPatterns
#-}
module Protocol
  ( apiRoutes
  ) where

import Data.Aeson
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
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Data.Time

import Muste
import qualified PGF

import Ajax
import qualified Database

-- FIXME Do not import this
import qualified Config

type Contexts = Map T.Text (Map String Context)

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

lessonHandler :: T.Text -> Protocol v w ServerMessage
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
getUser :: Protocol v w (T.Text, T.Text)
getUser = (\(CMLoginRequest usr pwd) -> (usr, pwd)) <$> getMessage

getConnection :: IO Connection
getConnection = Config.getDB >>= open

setLoginCookie
  :: T.Text -- ^ The token
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
  :: T.Text -- ^ Username
  -> T.Text -- ^ Password
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
  let lessonList = map (\(name,description,exercises,passedcount,score,time,passed,enabled) -> Lesson name description exercises passedcount score time passed enabled) lessons
  verifyMessage token (SMLessonsList lessonList)

handleLessonInit
  :: String -- ^ Token
  -> T.Text -- ^ Lesson
  -> Protocol v w ServerMessage
handleLessonInit token lesson =
  do
    contexts <- askContexts
    conn <- askConnection
    (sourceLang,sourceTree,targetLang,targetTree) <- liftIO $ Database.startLesson conn token lesson
    let (a,b) = assembleMenus contexts lesson (sourceLang,sourceTree) (targetLang,targetTree)
    verifyMessage token (SMMenuList lesson False 0 a b )

handleMenuRequest
  :: String -- ^ Token
  -> T.Text -- ^ Lesson
  -> Integer -- ^ Clicks
  -> UTCTime -- ^ Time
  -> ClientTree -- ^ Source tree
  -> ClientTree -- ^ Target tree
  -> Protocol v w ServerMessage
handleMenuRequest token lesson clicks time ctreea@(ClientTree langa treea) ctreeb@(ClientTree langb treeb) = do
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
  let (a , b) = act contexts lesson (langa , treea) (langb , treeb)
  verifyMessage token (SMMenuList lesson finished (succ clicks) a b)
  where
    finished :: Bool
    finished = treea == treeb

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

-- | Checks if a linearization token matches in both trees
matched :: Path -> TTree -> TTree -> Path
matched p t1 t2 = if selectNode t1 p == selectNode t2 p then p else []

-- | Gets the menus for a lesson, two trees and two languages
assembleMenus
  :: Contexts
  -> T.Text -- ^ Lesson
  -> (String,String)
  -> (String,String)
  -> (ServerTree,ServerTree)
assembleMenus contexts lesson (sourceLang,sourceTree) (targetLang,targetTree) = (a, b)
  where
  grammar = ctxtGrammar (contexts ! lesson ! sourceLang)
  sourceContext = contexts ! lesson ! sourceLang
  targetContext = contexts ! lesson ! targetLang
  sourceTTree = parseTTree grammar sourceTree
  targetTTree = parseTTree grammar targetTree
  tempSourceLin = linearizeTree sourceContext sourceTTree
  tempTargetLin = linearizeTree targetContext targetTTree
  sourceLin = map (\(LinToken path lin _) -> LinToken path lin (matched path sourceTTree targetTTree)) tempSourceLin
--          sourceMenu = Menu $ fromList $ map suggestionToCostTree $ suggestionFromPrecomputed (prec ! lesson ! (read sourceLang :: Language)) sourceTTree
  -- sourceMenu = Menu $ M.empty -- fromList $ map suggestionToCostTree $ getSuggestions sourceContext  sourceTTree
  sourceMenu = Menu $ getCleanMenu sourceContext sourceTTree
  targetLin = map (\(LinToken path lin _) -> LinToken path lin (matched path sourceTTree targetTTree)) tempTargetLin
--          targetMenu = Menu $ fromList $ filterCostTrees $ map suggestionToCostTree $ suggestionFromPrecomputed (prec ! lesson ! (read targetLang :: Language)) targetTTree
  targetMenu = Menu $ getCleanMenu targetContext targetTTree
-- At the moment the menu is not really a list of menus but instead a list with only one menu as the only element
  a = ServerTree sourceLang sourceTree sourceLin sourceMenu
  b = ServerTree targetLang targetTree targetLin targetMenu

emptyMenus
  :: Contexts
  -> T.Text
  -> (String,String)
  -> (String,String)
  -> (ServerTree,ServerTree)
emptyMenus contexts lesson (sourceLang,sourceTree) (targetLang,targetTree) =
  let
    grammar = ctxtGrammar (contexts ! lesson ! sourceLang)
    sourceTTree = parseTTree grammar sourceTree
    targetTTree = parseTTree grammar targetTree
    tempSourceLin = linearizeTree (contexts ! lesson ! sourceLang) sourceTTree
    tempTargetLin = linearizeTree (contexts ! lesson ! targetLang) targetTTree
    sourceLin = map (\(LinToken path lin _) -> LinToken path lin (matched path sourceTTree targetTTree)) tempSourceLin
    targetLin = map (\(LinToken path lin _) -> LinToken path lin (matched path sourceTTree targetTTree)) tempTargetLin
    a = ServerTree sourceLang sourceTree sourceLin (Menu M.empty)
    b = ServerTree targetLang targetTree targetLin (Menu M.empty)
  in
    (a,b)

-- TODO Wrap `PGF.*` methods in `Muste`.
initContexts
  :: MonadIO io
  => Connection
  -> io Contexts
initContexts conn = liftIO $ do
  lessonGrammarList <- Database.getLessons conn
  grammarList <- mapM readPGF lessonGrammarList
  preTuples <- mapM readLangs grammarList
  pure (M.fromList preTuples)
  where
  readPGF (lesson, _, grammarName, _srcLang, _trgLang, _, _, _) = do
    -- get all langs
    pgf <- PGF.readPGF (T.unpack grammarName)
    pure (lesson,Muste.pgfToGrammar pgf)
  readLangs (lesson, grammar) = do
    -- get all langs
    let langs = PGF.languages (Muste.pgf grammar)
    -- get all start trees
    let contexts = [(PGF.showCId lang, Muste.buildContext grammar lang) | lang <- langs]
    -- precompute for every lang and start tree
    pure (lesson, M.fromList contexts)
