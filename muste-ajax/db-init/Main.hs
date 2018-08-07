{-# LANGUAGE OverloadedStrings, CPP #-}
module Main (main) where

import Database.SQLite.Simple
#if MIN_VERSION_base(4,11,0)
#else
import Data.Semigroup (Semigroup((<>)))
#endif

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
  let exec_ = execute_ conn
  let exec q = execute conn q
  exec_ "DROP TABLE IF EXISTS User;"
  exec_ "DROP TABLE IF EXISTS Session;"
  exec_ "DROP TABLE IF EXISTS Lesson;"
  exec_ "DROP TABLE IF EXISTS Exercise;"
  exec_ "DROP TABLE IF EXISTS FinishedExercise;"
  exec_ "DROP TABLE IF EXISTS StartedLesson;"
  exec_ "DROP TABLE IF EXISTS FinishedLesson;"
  exec_ "DROP TABLE IF EXISTS ExerciseList"
  exec_ $
    "CREATE TABLE User (" <>
    "Username TEXT NOT NULL," <>
    "Password BLOB NOT NULL," <>
    "Salt BLOB NOT NULL," <>
    "Enabled BOOL NOT NULL DEFAULT 0," <>
    "PRIMARY KEY(Username));"
  exec_ $
    "CREATE TABLE Session (" <>
    "User TEXT NOT NULL REFERENCES User(Username)," <>
    "Token TEXT," <>
    "Starttime NUMERIC NOT NULL DEFAULT CURRENT_TIMESTAMP," <>
    "LastActive NUMERIC NOT NULL DEFAULT CURRENT_TIMESTAMP," <>
    "PRIMARY KEY(Token));"
  exec_ $
    "CREATE TABLE Exercise (" <>
    "SourceTree TEXT," <>
    "TargetTree TEXT," <>
    "Lesson TEXT," <>
    "Timeout NUMERIC NOT NULL DEFAULT 0," <>
    "PRIMARY KEY(SourceTree, TargetTree, Lesson)," <>
    "FOREIGN KEY(Lesson) References Lesson(Name));"
  exec_ $
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
  exec_ $
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
  exec_ $
    "CREATE TABLE StartedLesson (" <>
    "Lesson TEXT," <>
    "User TEXT," <>
    "Round NUMERIC NOT NULL DEFAULT 1," <>
    "PRIMARY KEY(Lesson, User, Round)," <>
    "FOREIGN KEY(Lesson) REFERENCES Lesson(Name), FOREIGN KEY(User) REFERENCES User(Username));"
  exec_ $
    "CREATE TABLE FinishedLesson (" <>
    "Lesson TEXT," <>
    "User TEXT," <>
    "Time NUMERIC NOT NULL," <>
    "ClickCount NUMERIC NOT NULL," <>
    "Round NUMERIC NOT NULL DEFAULT 1," <>
    "PRIMARY KEY (Lesson, User, Round)," <>
    "FOREIGN KEY (User) REFERENCES User(Username)," <>
    "FOREIGN KEY (Lesson) REFERENCES Lesson(Name));"
  exec_ $
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
  addUser "herbert" "HERBERT" True
  addUser "peter" "PETER" True
  let insertLessonQuery = "INSERT INTO Lesson (Name,Description,Grammar,SourceLanguage,TargetLanguage,ExerciseCount,Enabled,Repeatable) VALUES (?,?,?,?,?,?,?,?);" :: Query
  mapM_ (exec insertLessonQuery) Data.lessons
  let insertExerciseQuery = "INSERT INTO Exercise (SourceTree,TargetTree,Lesson) VALUES (?,?,?);" :: Query
  mapM_ (exec insertExerciseQuery) Data.exercises
