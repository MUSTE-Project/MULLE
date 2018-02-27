module Protocol where

import Ajax
import Database
import Muste
import Muste.Tree
import Muste.Grammar
import PGF
import Data.Map ((!),Map(..),fromList)
import qualified Data.Map.Lazy as M
import Control.Monad
import Control.Exception
import Database.SQLite.Simple
import Data.List
import Data.Maybe

handleClientRequest :: Connection -> Map String Grammar -> LessonsPrecomputed -> String -> IO String
handleClientRequest conn grammars prec body =
  do
    let cm = decodeClientMessage body
    catch (
      case cm of {
        CMLoginRequest user pass -> handleLoginRequest user pass ;
        -- CMMOTDRequest token -> handleMOTDRequest token
        -- CMDataRequest token context data -> handleDataRequest token context data
        CMLessonsRequest token -> handleLessonsRequest token ;
        CMLessonInit token lesson -> handleLessonInit token lesson grammars prec ;
        CMMenuRequest token lesson score time a b -> handleMenuRequest token lesson score time a b ;
        CMLogoutRequest token -> handleLogoutRequest token
        }
      )
      (\(DatabaseException msg) -> do { putStrLn $ "Exception: " ++ msg ; return $ encodeServerMessage SMLogoutResponse })
  where
    handleLoginRequest :: String -> String -> IO String
    handleLoginRequest user pass =
      do
        authed <- authUser conn user pass
        token <- startSession conn user
        return $ encodeServerMessage $ if authed then do SMLoginSuccess token else SMLoginFail
    handleLessonsRequest :: String -> IO String
    handleLessonsRequest token =
      do
        verified <- verifySession conn token
        lessons <- listLessons conn token
        let lessonList = map (\(name,description,exercises,passedcount,score,time,passed,enabled) -> Lesson name description exercises passedcount score time passed enabled) lessons
        returnVerifiedMessage verified (SMLessonsList lessonList)
    handleLessonInit :: String -> String -> Map String Grammar -> LessonsPrecomputed -> IO String
    handleLessonInit token lesson grammars prec =
      do
        verified <- verifySession conn token
        (sourceLang,sourceTree,targetLang,targetTree) <- startLesson conn token lesson
        let (a,b) = assembleMenus lesson (sourceLang,sourceTree) (targetLang,targetTree)
        returnVerifiedMessage verified (SMMenuList lesson False 0 a b )
    handleMenuRequest token lesson clicks time ctreea@(ClientTree langa treea) ctreeb@(ClientTree langb treeb)
    -- Check if finished here
      | treea == treeb =
        do
          verified <- verifySession conn token
          when (fst verified) (finishExercise conn token lesson time clicks)
          let (a,b) = emptyMenus lesson (langa,treea) (langb,treeb)
          returnVerifiedMessage verified (SMMenuList lesson True (clicks + 1) a b)
      | otherwise =
        do
          verified <- verifySession conn token
          let (a,b) = assembleMenus lesson (langa,treea) (langb,treeb)
          returnVerifiedMessage verified (SMMenuList lesson False (clicks + 1) a b )
    handleLogoutRequest token =
        do
          endSession conn token
          return $ encodeServerMessage SMLogoutResponse

    -- either encode a message or create an error message dependent on the outcome of the verification of the session
    tryVerified :: (Bool,String) -> ServerMessage -> ServerMessage
    tryVerified (True,_) m = m
    tryVerified (False,e) _ = (SMSessionInvalid e)
    returnVerifiedMessage v m = return $ encodeServerMessage $ tryVerified v m
    -- Checks if a linearization token matches in both trees
    matched p t1 t2 = if selectNode t1 p == selectNode t2 p then p else []
    -- gets the menus for a lesson, two trees and two languages
    assembleMenus :: String -> (String,String) -> (String,String) -> (ServerTree,ServerTree)
    assembleMenus lesson (sourceLang,sourceTree) (targetLang,targetTree) =
      let grammar = (grammars ! lesson)
          sourceContext = (grammars ! lesson,read sourceLang :: Language)
          targetContext = (grammars ! lesson,read targetLang :: Language)
          sourceTTree = gfAbsTreeToTTree grammar (read sourceTree :: Tree)
          targetTTree = gfAbsTreeToTTree grammar (read targetTree :: Tree)
          tempSourceLin = linearizeTree (grammar,read sourceLang :: Language) sourceTTree
          tempTargetLin = linearizeTree (grammar,read targetLang :: Language) targetTTree
          sourceLin = map (\(path,lin) -> LinToken path lin (matched path sourceTTree targetTTree)) tempSourceLin
--          sourceMenu = Menu $ fromList $ map suggestionToCostTree $ suggestionFromPrecomputed (prec ! lesson ! (read sourceLang :: Language)) sourceTTree
          sourceMenu = Menu $ M.empty -- fromList $ map suggestionToCostTree $ getSuggestions sourceContext  sourceTTree 
          targetLin = map (\(path,lin) -> LinToken path lin (matched path sourceTTree targetTTree)) tempTargetLin
--          targetMenu = Menu $ fromList $ filterCostTrees $ map suggestionToCostTree $ suggestionFromPrecomputed (prec ! lesson ! (read targetLang :: Language)) targetTTree
          targetMenu = Menu $ getCleanMenu targetContext targetTTree
        -- At the moment the menu is not really a list of menus but instead a list with only one menu as the only element
          a = ServerTree sourceLang sourceTree sourceLin sourceMenu
          b = ServerTree targetLang targetTree targetLin targetMenu
      in
        (a,b)
    emptyMenus :: String -> (String,String) -> (String,String) -> (ServerTree,ServerTree)
    emptyMenus lesson (sourceLang,sourceTree) (targetLang,targetTree) =
      let
        grammar = (grammars ! lesson)
        sourceTTree = gfAbsTreeToTTree grammar (read sourceTree :: Tree)
        targetTTree = gfAbsTreeToTTree grammar (read targetTree :: Tree)
        tempSourceLin = linearizeTree (grammar,read sourceLang :: Language) sourceTTree
        tempTargetLin = linearizeTree (grammar,read targetLang :: Language) targetTTree
        sourceLin = map (\(path,lin) -> LinToken path lin (matched path sourceTTree targetTTree)) tempSourceLin
        targetLin = map (\(path,lin) -> LinToken path lin (matched path sourceTTree targetTTree)) tempTargetLin
        a = ServerTree sourceLang sourceTree sourceLin (Menu M.empty)
        b = ServerTree targetLang targetTree targetLin (Menu M.empty)
      in
        (a,b)
  
