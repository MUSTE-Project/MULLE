{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Data.String
import Database.SQLite.Simple

import qualified Config
import qualified Database

import qualified Data

main :: IO ()
main = do
  putStrLn "Initializing database..."
  db <- Config.getDB
  withConnection db initDB
  putStrLn "Initializing database... done"

initDB :: Connection -> IO ()
initDB conn = do
  let exec = execute_ conn
  exec "DROP TABLE IF EXISTS User;"
  exec "DROP TABLE IF EXISTS Session;"
  exec "DROP TABLE IF EXISTS Lesson;"
  exec "DROP TABLE IF EXISTS Exercise;"
  exec "DROP TABLE IF EXISTS FinishedExercise;"
  exec "DROP TABLE IF EXISTS StartedLesson;"
  exec "DROP TABLE IF EXISTS FinishedLesson;"
  exec "DROP TABLE IF EXISTS ExerciseList"
  exec $
    "CREATE TABLE User (" <>
    "Username TEXT NOT NULL," <>
    "Password BLOB NOT NULL," <>
    "Salt BLOB NOT NULL," <>
    "Enabled BOOL NOT NULL DEFAULT 0," <>
    "PRIMARY KEY(Username));"
  exec $
    "CREATE TABLE Session (" <>
    "User TEXT NOT NULL REFERENCES User(Username)," <>
    "Token TEXT," <>
    "Starttime NUMERIC NOT NULL DEFAULT CURRENT_TIMESTAMP," <>
    "LastActive NUMERIC NOT NULL DEFAULT CURRENT_TIMESTAMP," <>
    "PRIMARY KEY(Token));"
  exec $
    "CREATE TABLE Exercise (" <>
    "SourceTree TEXT," <>
    "TargetTree TEXT," <>
    "Lesson TEXT," <>
    "Timeout NUMERIC NOT NULL DEFAULT 0," <>
    "PRIMARY KEY(SourceTree, TargetTree, Lesson)," <>
    "FOREIGN KEY(Lesson) References Lesson(Name));"
  exec $
    "CREATE TABLE Lesson (" <>
    "Name TEXT," <>
    "Description TEXT NOT NULL," <>
    "Grammar TEXT NOT NULL," <>
    "SourceLanguage TEXT NOT NULL," <>
    "TargetLanguage TEXT NOT NULL," <>
    "ExerciseCount NUMERIC NOT NULL," <>
    "Enabled BOOL NOT NULL DEFAULT 0," <>
    "Repeatable BOOL NOT NULL DEFAULT 1," <>
    "PRIMARY KEY(Name));"
  exec $
    "CREATE TABLE FinishedExercise (" <>
    "User TEXT," <>
    "SourceTree TEXT," <>
    "TargetTree TEXT," <>
    "Lesson TEXT," <>
    "Time NUMERIC NOT NULL," <>
    "ClickCount NUMERIC NOT NULL," <>
    "Round NUMERIC NOT NULL," <>
    "PRIMARY KEY (User,SourceTree, TargetTree, Lesson, Round)," <>
    "FOREIGN KEY (User) REFERENCES User(Username)," <>
    "FOREIGN KEY(SourceTree, TargetTree, Lesson) REFERENCES Exercise(SourceTree, TargetTree, Lesson));"
  exec $
    "CREATE TABLE StartedLesson (" <>
    "Lesson TEXT," <>
    "User TEXT," <>
    "Round NUMERIC NOT NULL DEFAULT 1," <>
    "PRIMARY KEY(Lesson, User, Round)," <>
    "FOREIGN KEY(Lesson) REFERENCES Lesson(Name), FOREIGN KEY(User) REFERENCES User(Username));"
  exec $
    "CREATE TABLE FinishedLesson (" <>
    "Lesson TEXT," <>
    "User TEXT," <>
    "Time NUMERIC NOT NULL," <>
    "ClickCount NUMERIC NOT NULL," <>
    "Round NUMERIC NOT NULL DEFAULT 1," <>
    "PRIMARY KEY (Lesson, User, Round)," <>
    "FOREIGN KEY (User) REFERENCES User(Username)," <>
    "FOREIGN KEY (Lesson) REFERENCES Lesson(Name));"
  exec $
    "CREATE TABLE ExerciseList (" <>
    "User TEXT," <>
    "SourceTree TEXT," <>
    "TargetTree TEXT," <>
    "Lesson TEXT," <>
    "Round NUMERIC NOT NULL DEFAULT 1," <>
    "PRIMARY KEY (User, SourceTree, TargetTree, Lesson, Round)," <>
    "FOREIGN KEY(User) REFERENCES User(Username)," <>
    "FOREIGN KEY(SourceTree,TargetTree, Lesson) REFERENCES Exercise (SourceTree, TargetTree, Lesson));"
  let addUser = Database.addUser conn
  addUser "herbert" "HERBERT" 1
  addUser "peter" "PETER" 1
  let insertLessonQuery = "INSERT INTO Lesson (Name,Description,Grammar,SourceLanguage,TargetLanguage,ExerciseCount,Enabled,Repeatable) VALUES (?,?,?,?,?,?,?,?);" :: Query
  lessonData <- Data.getLessons
  mapM_ (execute conn insertLessonQuery) lessonData
  let insertExerciseQuery = "INSERT INTO Exercise (SourceTree,TargetTree,Lesson) VALUES (?,?,?);" :: Query
  mapM_ (execute conn insertExerciseQuery) $ (\(a, b, c) -> (show a, show b, c)) <$> Data.exercises
  -- let insertFinishedExerciseQuery = "INSERT INTO FinishedExercise (User,SourceTree,TargetTree,Lesson,Time,ClickCount,Round) VALUES ('herbert','useS (useCl (simpleCl (useCNindefsg (useN vinum_N)) (complA sapiens_A)))','useS (useCl (simpleCl (usePron he_PP) (complA sapiens_A)))','Prima Pars',15,5,1);" :: Query
  -- exec insertFinishedExerciseQuery
