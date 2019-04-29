{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language
 OverloadedStrings
#-}

module Muste.Web.DbInit (initDb) where

import System.Directory (createDirectoryIfMissing)
import System.FilePath (takeDirectory, (</>))

import Database.SQLite.Simple (Connection(Connection))
import qualified Database.SQLite.Simple as SQL
import qualified Database.SQLite3 as SQL

import Data.Text (Text)
import qualified Data.Text as Text

import qualified Muste.Web.Config as Config
import qualified Muste.Web.Handlers.Session as Session


initDb :: Config.AppConfig -> IO ()
initDb cfg = do
  let dbFile = Config.cfgDir cfg </> Config.db cfg
  putStrLn $ ">> Initializing database: " ++ dbFile
  mkParDir dbFile
  SQL.withConnection dbFile (initDbAux cfg)
  putStrLn "<< Initializing database: OK\n"


-- | @'mkParDir' p@ Ensure that the directory that @p@ is in is
-- created like the linux command @mkdir -p@.
mkParDir :: FilePath -> IO ()
mkParDir = createDirectoryIfMissing True . takeDirectory


initDbAux :: Config.AppConfig -> Connection -> IO ()
initDbAux cfg conn
  = do createTables conn [userTable, sessionTable, cmplExerciseTable, cmplLessonTable]
       mapM_ (dropRecreateUser conn) (Config.users cfg)


dropRecreateUser :: Connection -> Config.InitialUser -> IO ()
dropRecreateUser conn (Config.User name pwd)
  = do putStrLn $ "Adding user: " ++ show name ++ ", pwd: " ++ show pwd
       Session.addUser conn name pwd


userTable :: SQLTable
userTable = SQLTable "User"
            [ SQLRow "Username" "TEXT" "NOT NULL PRIMARY KEY"
            , SQLRow "Password" "BLOB" "NOT NULL"
            , SQLRow "Salt"     "BLOB" "NOT NULL"
            ]

sessionTable :: SQLTable
sessionTable = SQLTable "Session"
               [ SQLRow "User"       "TEXT"    "NOT NULL UNIQUE"
               , SQLRow "Token"      "TEXT"    "NOT NULL PRIMARY KEY"
               , SQLRow "Starttime"  "NUMERIC" "NOT NULL DEFAULT CURRENT_TIMESTAMP"
               , SQLRow "LastActive" "NUMERIC" "NOT NULL DEFAULT CURRENT_TIMESTAMP"
               , SQLForeignKey "User" "User" "Username"
               ]

cmplExerciseTable :: SQLTable
cmplExerciseTable = SQLTable "CompletedExercise"
               [ SQLRow "User"      "TEXT"    "NOT NULL"
               , SQLRow "Lesson"    "TEXT"    "NOT NULL"
               , SQLRow "Exercise"  "INTEGER" "NOT NULL"
               , SQLRow "Score"     "NUMERIC" "NOT NULL DEFAULT 0"
               , SQLRow "Timestamp" "NUMERIC" "NOT NULL DEFAULT CURRENT_TIMESTAMP"
               , SQLUnique ["User", "Lesson", "Exercise"]
               , SQLForeignKey "User" "User" "Username"
               ]

cmplLessonTable :: SQLTable
cmplLessonTable = SQLTable "CompletedLesson"
               [ SQLRow "User"      "TEXT"    "NOT NULL"
               , SQLRow "Lesson"    "TEXT"    "NOT NULL"
               , SQLRow "Score"     "NUMERIC" "NOT NULL DEFAULT 0"
               , SQLRow "Timestamp" "NUMERIC" "NOT NULL DEFAULT CURRENT_TIMESTAMP"
               , SQLForeignKey "User" "User" "Username"
               ]


type SQLName = Text
type SQLType = Text
data SQLTable = SQLTable SQLName [SQLRow]
data SQLRow = SQLRow SQLName SQLType Text
            | SQLUnique [SQLName]
            | SQLForeignKey SQLName SQLName SQLName


createTables :: Connection -> [SQLTable] -> IO ()
createTables (Connection db) tables
  = do putStrLn $ "Creating tables: " ++ show [name | SQLTable name _ <- tables]
       SQL.exec db $ Text.unlines $
         ["BEGIN TRANSACTION;"] ++
         map textCreateTable tables ++ 
         ["COMMIT TRANSACTION;"]


textCreateTable :: SQLTable -> Text
textCreateTable (SQLTable name rows)
  = Text.unwords [ "DROP TABLE IF EXISTS", name, ";\n"
                 , "CREATE TABLE", name, "(\n"
                 , Text.intercalate ",\n" (map textRow rows), "\n"
                 , ");\n"
                 ]


textRow :: SQLRow -> Text
textRow (SQLRow name typ extra) 
  = Text.unwords [name, typ, extra]
textRow (SQLUnique names)
  = Text.unwords ["UNIQUE (", Text.intercalate ", " names, ")"]
textRow (SQLForeignKey name reftbl refname)
  = Text.unwords ["FOREIGN KEY (", name, ") REFERENCES", reftbl, "(", refname, ")"]

