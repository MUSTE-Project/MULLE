{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language
 OverloadedStrings
#-}

module Muste.Web.Handlers.Results
  ( addCompletedExercise
  , getCompletedExercises
  , addCompletedLesson
  , getCompletedLessons
  , getHighscores
  ) where

import qualified Control.Exception.Lifted as CL

import Database.SQLite.Simple (NamedParam(..), FromRow(..), field)
import qualified Database.SQLite.Simple as SQL

import Data.Aeson ((.=), (.:), FromJSON(parseJSON), ToJSON(toJSON))
import qualified Data.Aeson as Aeson
import qualified Data.Time.Clock as Time
import Data.Text (Text)
import Data.List (groupBy)

import qualified Muste.Web.Class as MULLError (MULLError(..))
import Muste.Web.Class (MULLE, wrapConnection)
import Muste.Web.Handlers.Session
  ( verifySession
  , Token
  , SessionToken(..)
  , SessionTokenOnly(..)
  )


--------------------------------------------------------------------------------
-- /add-completed-exercise
-- /get-completed-exercises

addCompletedExercise :: SessionToken CompletedExercise -> MULLE v ()
addCompletedExercise (SessionToken token (CompletedExercise lesson exercise score))
  = verifyWrapConnection token $ \conn ->
    do user <- getUsername conn token
       timestamp <- Time.getCurrentTime
       SQL.executeNamed conn
         " INSERT OR REPLACE INTO CompletedExercise \
         \        (User, Lesson, Exercise, Score, Timestamp) \
         \ VALUES (:User, :Lesson, :Exercise, :Score, :Timestamp) "
         [ ":User"      := user
         , ":Lesson"    := lesson
         , ":Exercise"  := exercise
         , ":Score"     := score
         , ":Timestamp" := timestamp
         ]


getCompletedExercises :: SessionTokenOnly -> MULLE v [CompletedExercise]
getCompletedExercises (SessionTokenOnly token) 
  = verifyWrapConnection token $ \conn ->
    do user <- getUsername conn token
       SQL.queryNamed conn
         " SELECT Lesson, Exercise, Score \
         \ FROM CompletedExercise WHERE User = :User "
         [":User" := user]


data CompletedExercise = CompletedExercise Text Int Int

instance FromRow CompletedExercise where
  fromRow = CompletedExercise <$> field <*> field <*> field

instance FromJSON CompletedExercise where
  parseJSON = Aeson.withObject "CompletedExercise" $
    \v -> CompletedExercise <$> v .: "lesson" <*> v .: "exercise" <*> v .: "score"

instance ToJSON CompletedExercise where
  toJSON (CompletedExercise lesson exercise score) =
    Aeson.object ["lesson" .= lesson, "exercise" .= exercise, "score" .= score]


--------------------------------------------------------------------------------
-- /add-completed-lesson
-- /get-completed-lessons

addCompletedLesson :: SessionToken CompletedLesson -> MULLE v ()
addCompletedLesson (SessionToken token (CompletedLesson lesson score))
  = verifyWrapConnection token $ \conn ->
    do user <- getUsername conn token
       timestamp <- Time.getCurrentTime
       SQL.executeNamed conn
         " INSERT INTO CompletedLesson (User, Lesson, Score, Timestamp) \
         \ VALUES (:User, :Lesson, :Score, :Timestamp) "
         [ ":User"      := user
         , ":Lesson"    := lesson
         , ":Score"     := score
         , ":Timestamp" := timestamp
         ]
       SQL.executeNamed conn
         " DELETE FROM CompletedExercise \
         \ WHERE User = :User AND Lesson = :Lesson "
         [ ":User"      := user
         , ":Lesson"    := lesson
         ]       


getCompletedLessons :: SessionTokenOnly -> MULLE v [CompletedLesson]
getCompletedLessons (SessionTokenOnly token) 
  = verifyWrapConnection token $ \conn ->
    do user <- getUsername conn token
       SQL.queryNamed conn
         " SELECT Lesson, Score \
         \ FROM CompletedLesson WHERE User = :User "
         [":User" := user]


data CompletedLesson = CompletedLesson Text Int

instance FromRow CompletedLesson where
  fromRow = CompletedLesson <$> field <*> field

instance FromJSON CompletedLesson where
  parseJSON = Aeson.withObject "CompletedLesson" $
    \v -> CompletedLesson <$> v .: "lesson" <*> v .: "score"

instance ToJSON CompletedLesson where
  toJSON (CompletedLesson lesson score) =
    Aeson.object ["lesson" .= lesson, "score" .= score]


--------------------------------------------------------------------------------
-- get-highscores

getHighscores :: SessionTokenOnly -> MULLE v [HighScore]
getHighscores (SessionTokenOnly token) 
  = verifyWrapConnection token $ \conn ->
    do lessons <- SQL.query_ conn " SELECT Lesson, Score, User FROM CompletedLesson "
       let grouped_lesson_scores = groupBy same lessons
       return [ maximum scores | scores <- grouped_lesson_scores ]
  where
    same (HighScore lesson1 _ _) (HighScore lesson2 _ _) = lesson1 == lesson2


data HighScore = HighScore Text Int Text
                 deriving (Eq, Ord)

instance FromRow HighScore where
  fromRow = HighScore <$> field <*> field <*> field

instance FromJSON HighScore where
  parseJSON = Aeson.withObject "HighScore" $
    \v -> HighScore <$> v .: "lesson" <*> v .: "score" <*> v .: "user"

instance ToJSON HighScore where
  toJSON (HighScore lesson score user) =
    Aeson.object ["lesson" .= lesson, "score" .= score, "user" .= user]


--------------------------------------------------------------------------------
-- tools

verifyWrapConnection :: Token -> (SQL.Connection -> IO a) -> MULLE v a
verifyWrapConnection token action
  = verifySession token >> wrapConnection action


getUsername :: SQL.Connection -> Token -> IO Text
getUsername conn token = do
  xs <- SQL.queryNamed conn
        "SELECT User FROM Session WHERE Token = :Token"
        [":Token" := token]
  case xs of
    [SQL.Only x] -> return x
    _ -> CL.throwIO MULLError.NoCurrentSession

