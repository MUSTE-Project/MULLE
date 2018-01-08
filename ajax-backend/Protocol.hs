module Protocol where

import Ajax
import Database
import Muste
import Muste.Tree
import Muste.Grammar
import PGF
import Data.Map ((!),Map(..),fromList)

import Database.SQLite.Simple

handleClientRequest :: Connection -> Map String Grammar -> LessonsPrecomputed -> String -> IO String
handleClientRequest conn grammars prec body =
  do
    let cm = decodeClientMessage body
    case cm of {
      CMLoginRequest user pass -> handleLoginRequest user pass ;
      -- CMMOTDRequest token -> handleMOTDRequest token
      -- CMDataRequest token context data -> handleDataRequest token context data
      CMLessonsRequest token -> handleLessonsRequest token ;
      CMLessonInit token lesson -> handleLessonInit token lesson grammars prec ;
      CMMenuRequest token lesson score time a b -> handleMenuRequest token lesson score time a b
      }
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
        let lessonList = map (\(name,description,exercises,passed) -> Lesson name description exercises passed) lessons
        returnVerifiedMessage verified (SMLessonsList lessonList)
    handleLessonInit :: String -> String -> Map String Grammar -> LessonsPrecomputed -> IO String
    handleLessonInit token lesson grammars prec =
      do
        verified <- verifySession conn token
        (sourceLang,sourceTree,targetLang,targetTree) <- startLesson conn token lesson
        let grammar = (grammars ! lesson)
        let sourceTTree = gfAbsTreeToTTree grammar (read sourceTree :: Tree)
        let targetTTree = gfAbsTreeToTTree grammar (read targetTree :: Tree)
        let tempSourceLin = linearizeTree (grammar,read sourceLang :: Language) sourceTTree
        let tempTargetLin = linearizeTree (grammar,read sourceLang :: Language) targetTTree
        let sourceLin = map (\(path,lin) -> LinToken path lin (matched path sourceTTree targetTTree) tempSourceLin
        let sourceMenu = Menu $ fromList $ map suggestionToCostTree $ suggestionFromPrecomputed (prec ! lesson ! (read sourceLang :: Language)) sourceTTree 
        let targetLin = []
        let targetMenu = Menu $ fromList $ map suggestionToCostTree $ suggestionFromPrecomputed (prec ! lesson ! (read targetLang :: Language)) targetTTree 
        let a = ServerTree sourceLang sourceTree sourceLin sourceMenu
        let b = ServerTree targetLang targetTree targetLin targetMenu
        returnVerifiedMessage verified (SMMenuList lesson False 0 a b )
        return "TODO"
    handleMenuRequest token lesson score time a b =
      return "TODO"
    -- either encode a message or create an error message dependent on the outcome of the verification of the session
    tryVerified :: (Bool,String) -> ServerMessage -> ServerMessage
    tryVerified (True,_) m = m
    tryVerified (False,e) _ = (SMSessionInvalid e)
    returnVerifiedMessage v m = return $ encodeServerMessage $ tryVerified v m
    -- Convert between the muste suggestion output and the ajax cost trees
    suggestionToCostTree :: (Path, [(Int,[(Path,String)],TTree)]) -> (Path,[[CostTree]])
    suggestionToCostTree (path,trees) =
      (path, [map (\(cost,lin,tree) -> CostTree cost (map (uncurry Linearization) lin) (show $ ttreeToGFAbsTree tree)) trees])
    -- Checks if a linearization token matches in both trees
    matched p t1 t2 = if selectNode p t1 == selectNode p t2 then p else []

