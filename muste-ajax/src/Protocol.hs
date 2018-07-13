module Protocol where

import Ajax
import Database
import Muste
import Muste.Tree
import Muste.Grammar (parseTTree)
import Muste.Linearization

import Data.Map ((!),Map)
import qualified Data.Map.Lazy as M
import Control.Monad
import Control.Exception
import Database.SQLite.Simple
import Control.Monad.Reader

type Contexts = Map String (Map String Context)

data Env = Env
  { connection :: Connection
  , contexts   :: Contexts
  }

type App a = ReaderT Env IO a

handleClientRequest :: Connection -> Map String (Map String Context) -> String -> IO String
handleClientRequest conn contexts body =
  do
    let cm = decodeClientMessage body
    catch (
      (`runReaderT` (Env conn contexts)) $ case cm of {
        CMLoginRequest user pass -> handleLoginRequest user pass ;
        -- CMMOTDRequest token -> handleMOTDRequest token
        -- CMDataRequest token context data -> handleDataRequest token context data
        CMLessonsRequest token -> handleLessonsRequest token ;
        CMLessonInit token lesson -> handleLessonInit contexts token lesson ;
        CMMenuRequest token lesson score time a b -> handleMenuRequest contexts token lesson score time a b ;
        CMLogoutRequest token -> handleLogoutRequest token ;
        _ -> error "Protocol.handleClientRequest: Non exhaustive pattern match"
        }
      )
      (\(DatabaseException msg) -> do { putStrLn $ "Exception: " ++ msg ; return $ encodeServerMessage SMLogoutResponse })

handleLoginRequest
  :: String -- ^ Username
  -> String -- ^ Password
  -> App String
handleLoginRequest user pass = do
  c <- askConnection
  authed <- lift $ authUser c user pass
  token  <- lift $ startSession c user
  pure $ encodeServerMessage
    $ if authed then SMLoginSuccess token else SMLoginFail

askConnection :: App Connection
askConnection = asks connection

handleLessonsRequest :: String -> App String
handleLessonsRequest token =
  do
    conn <- askConnection
    verified <- lift $ verifySession conn token
    lessons <- lift $ listLessons conn token
    let lessonList = map (\(name,description,exercises,passedcount,score,time,passed,enabled) -> Lesson name description exercises passedcount score time passed enabled) lessons
    returnVerifiedMessage verified (SMLessonsList lessonList)

handleLessonInit
  :: Map String (Map String Context)
  -> String
  -> String
  -> App String
handleLessonInit contexts token lesson =
  do
    conn <- askConnection
    verified <- lift $ verifySession conn token
    (sourceLang,sourceTree,targetLang,targetTree) <- lift $ startLesson conn token lesson
    let (a,b) = assembleMenus contexts lesson (sourceLang,sourceTree) (targetLang,targetTree)
    returnVerifiedMessage verified (SMMenuList lesson False 0 a b )

handleMenuRequest :: Map String (Map String Context)
  -> String
  -> String
  -> Int
  -> Int
  -> ClientTree
  -> ClientTree
  -> App String
handleMenuRequest contexts token lesson clicks time ctreea@(ClientTree langa treea) ctreeb@(ClientTree langb treeb) = do
  conn <- askConnection
  verified <- lift $ verifySession conn token
-- Check if finished here
  if treea == treeb
  then
    do
      -- verified <- verifySession conn token
      when (fst verified) (lift $ finishExercise conn token lesson time clicks)
      let (a,b) = emptyMenus contexts lesson (langa,treea) (langb,treeb)
      returnVerifiedMessage verified (SMMenuList lesson True (clicks + 1) a b)
  else
    do
      -- verified <- verifySession conn token
      let (a,b) = assembleMenus contexts lesson (langa,treea) (langb,treeb)
      returnVerifiedMessage verified (SMMenuList lesson False (clicks + 1) a b )

handleLogoutRequest :: String -> App String
handleLogoutRequest token =
    do
      conn <- askConnection
      lift $ endSession conn token
      return $ encodeServerMessage SMLogoutResponse

-- | either encode a message or create an error message dependent on the outcome of the verification of the session
tryVerified :: (Bool,String) -> ServerMessage -> ServerMessage
tryVerified (True,_) m = m
tryVerified (False,e) _ = (SMSessionInvalid e)

returnVerifiedMessage :: Monad m => (Bool, String) -> ServerMessage -> m String
returnVerifiedMessage v m = return $ encodeServerMessage $ tryVerified v m

-- | Checks if a linearization token matches in both trees
matched :: Path -> TTree -> TTree -> Path
matched p t1 t2 = if selectNode t1 p == selectNode t2 p then p else []

-- | Gets the menus for a lesson, two trees and two languages
assembleMenus :: Map String (Map String Context) -> String -> (String,String) -> (String,String) -> (ServerTree,ServerTree)
assembleMenus contexts lesson (sourceLang,sourceTree) (targetLang,targetTree) =
  let grammar = (\(g,_,_) -> g) (contexts ! lesson ! sourceLang)
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
  in
    (a,b)

emptyMenus :: Map String (Map String Context) -> String -> (String,String) -> (String,String) -> (ServerTree,ServerTree)
emptyMenus contexts lesson (sourceLang,sourceTree) (targetLang,targetTree) =
  let
    grammar = (\(g,_,_) -> g) (contexts ! lesson ! sourceLang)
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
