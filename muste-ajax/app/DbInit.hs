{-# LANGUAGE OverloadedStrings, CPP, UnicodeSyntax, TemplateHaskell, QuasiQuotes, TypeApplications #-}
module DbInit (initDb) where

import           Data.ByteString (ByteString)
import           Data.FileEmbed (embedFile)
import           Data.Text (Text)
import           Data.Text.Encoding (decodeUtf8)
import qualified Database
import           Database.SQLite.Simple (Connection(Connection), Query)
import qualified Database.SQLite.Simple as SQL
import           Database.SQLite.Simple.QQ (sql)
import qualified Database.SQLite3 as SQL
import           System.Directory (createDirectoryIfMissing)
import           System.FilePath (takeDirectory)
import           Text.Printf
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.FileEmbed

import qualified DbInit.Data as Data
import qualified Config

import Muste (TTree, Linearization, Context)
import qualified Muste.Linearization as Linearization (langAndContext, mkLin)

initDb :: IO ()
initDb = do
  putStrLn "Initializing database..."
  mkParDir Config.db
  SQL.withConnection Config.db initDB
  putStrLn "Initializing database... done"

-- | @'mkParDir' p@ Ensure that the directory that @p@ is in is
-- created.
mkParDir ∷ FilePath → IO ()
mkParDir = createDirectoryIfMissing True . takeDirectory

initScript ∷ ByteString
initScript = $(makeRelativeToProject "data/sql/create.sql" >>= embedFile)

execRaw ∷ Connection → Text → IO ()
execRaw (Connection db) qry = SQL.exec db qry

initDB ∷ Connection → IO ()
initDB conn = do
  let exec ∷ SQL.ToRow q ⇒ Query → q → IO ()
      exec p = SQL.execute conn p
  execRaw conn $ decodeUtf8 initScript
  mapM_ (addUser conn) users
  mapM_ (exec insertLessonQuery)   Data.lessons
  mapM_ (exec insertExerciseQuery) exercises

exercises ∷ [(Linearization, Linearization, String)]
exercises = Data.exercises >>= mkExercise
  where
  mkExercise ∷ (String, String, String, String, [(TTree, TTree)])
    → [(Linearization, Linearization, String)]
  mkExercise (idfG, idfL, srcL, trgL, xs)
    = go (lin srcL) (lin trgL) idfL <$> xs
    where
    ctxt = Linearization.langAndContext idfG
    lang ∷ String → Context
    lang idf = fromMaybe (error $ printf "Lang not found: %s" idf)
      $ Map.lookup idf ctxt
    lin ∷ String → TTree → TTree → TTree → Linearization
    lin l = Linearization.mkLin (lang l)
  go ∷ (TTree → TTree → TTree → Linearization) → (TTree → TTree → TTree → Linearization)
    → String → (TTree, TTree)
    → (Linearization, Linearization, String)
  go srcC trgC idfE (src, trg) = (srcC src trg src, trgC src trg trg, idfE)

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
