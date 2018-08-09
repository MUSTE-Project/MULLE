{-# LANGUAGE OverloadedStrings, CPP, UnicodeSyntax, TemplateHaskell, QuasiQuotes, TypeApplications #-}
module Main (main) where

import           Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as ByteString
import           Data.FileEmbed (embedFile)
import           Data.Text (Text)
import           Data.Text.Encoding (decodeUtf8)
import qualified Data.Yaml as Yaml (encode)
import qualified Database
import           Database.SQLite.Simple (Connection(Connection), Query)
import qualified Database.SQLite.Simple as SQL
import           Database.SQLite.Simple.QQ (sql)
import qualified Database.SQLite3 as SQL
import           System.Directory (createDirectoryIfMissing)
import           System.FilePath (takeDirectory)
import           Text.Printf

import qualified Data
import qualified Config

main :: IO ()
main = do
  putStrLn "Initializing database..."
  showConfig
  mkParDir Config.db
  SQL.withConnection Config.db initDB
  putStrLn "Initializing database... done"

showConfig ∷ IO ()
showConfig = do
  printf "[Configurations options]\n"
  printf $ ByteString.unpack $ Yaml.encode $ Config.appConfig

-- | @'mkParDir' p@ Ensure that the directory that @p@ is in is
-- created.
mkParDir ∷ FilePath → IO ()
mkParDir = createDirectoryIfMissing True . takeDirectory

initScript ∷ ByteString
initScript = $(embedFile "data/sql/create.sql")

execRaw ∷ Connection → Text → IO ()
execRaw (Connection db) qry = SQL.exec db qry

initDB ∷ Connection → IO ()
initDB conn = do
  let exec p = SQL.execute conn p
  putStrLn $ ByteString.unpack initScript
  execRaw conn $ decodeUtf8 initScript
  mapM_ (addUser conn) users
  mapM_ (exec insertLessonQuery)   Data.lessons
  mapM_ (exec insertExerciseQuery) Data.exercises

addUser ∷ Connection → (Text, Text, Bool) → IO ()
addUser c (usr,psw,active) = Database.addUser c usr psw active

users ∷ [(Text, Text, Bool)]
users =
  [ ("herbert", "HERBERT", True)
  , ("peter",   "PETER",   True)
  ]

insertLessonQuery ∷ Query
insertLessonQuery
  = [sql|
        INSERT INTO Lesson
        (Name,Description,Grammar,SourceLanguage,TargetLanguage,ExerciseCount,Enabled,Repeatable)
        VALUES (?,?,?,?,?,?,?,?);
     |]

insertExerciseQuery ∷ Query
insertExerciseQuery
  = [sql|
        INSERT INTO Exercise
        (SourceTree,TargetTree,Lesson)
        VALUES (?,?,?);
    |]
