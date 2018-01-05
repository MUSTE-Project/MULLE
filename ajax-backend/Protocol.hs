module Protocol where

import Ajax
import Database
import Muste hiding (linearizeTree)
import Muste.Grammar

import Database.SQLite.Simple


handleClientRequest :: Connection -> Grammar -> Precomputed -> String -> IO String
handleClientRequest conn grammar prec body =
  do
    let cm = decodeClientMessage body
    case cm of {
      CMLoginRequest user pass -> handleLoginRequest user pass ;
      CMLessonsRequest token -> handleLessonsRequest token,
      CMLessonInit token lesson -> handleLessonInit token lesson
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
        return $ encodeServerMessage $ tryVerified verified (SMLessonsList lessonList)
    handleLessonInit :: String -> String -> IO String
    handleLessonInit token lesson =
      do
        verified <- verifySession conn token
        startLesson conn token lesson
    tryVerified :: (Bool,String) -> ServerMessage -> ServerMessage
    tryVerified (True,_) m = m
    tryVerified (False,e) _ = (SMSessionInvalid e)
