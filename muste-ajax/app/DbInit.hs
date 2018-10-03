{-# LANGUAGE OverloadedStrings, UnicodeSyntax, TemplateHaskell,
  QuasiQuotes, TypeApplications, RecordWildCards, OverloadedLists #-}
{-# OPTIONS_GHC -Wall #-}
module DbInit (initDb) where

import           Prelude ()
import           Muste.Prelude
import           Data.ByteString (ByteString)
import           Data.FileEmbed (embedFile)
import           Data.Text.Encoding (decodeUtf8)
import qualified Database
import           Database.SQLite.Simple (Connection(Connection), Query)
import qualified Database.SQLite.Simple as SQL
import           Database.SQLite.Simple.QQ (sql)
import qualified Database.SQLite3 as SQL
import           System.Directory (createDirectoryIfMissing)
import           System.FilePath (takeDirectory)
import           Data.FileEmbed
import           Data.Vector (Vector)

import qualified DbInit.Data as Data
import qualified Config

import           Muste.Sentence.Unannotated (Unannotated)
import qualified Muste.Sentence.Unannotated as Unannotated

initDb :: IO ()
initDb = do
  putStrLn "Initializing database..."
  mkParDir Config.db
  SQL.withConnection Config.db initDB
  putStrLn "Initializing database... done"

-- | @'mkParDir' p@ Ensure that the directory that @p@ is in is
-- created like the linux command @mkdir -p@.
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
  mapM_ (dropRecreateUser conn) users
  mapM_ (exec insertLessonQuery) Data.lessons
  mapM_ (exec insertExerciseQuery) exercises

exercises ∷ Vector (Unannotated, Unannotated, Text)
exercises = Data.exercises >>= go
  where
  go ∷ (Text, Text, Text, Text, Vector (Text, Text))
     → Vector (Unannotated, Unannotated, Text)
  go (g, n, srcL, trgL, xs) = step g n srcL trgL <$> xs
  step
    ∷ Text
    → Text
    → Text
    → Text
    → (Text, Text)
    → (Unannotated, Unannotated, Text)
  step g n srcL trgL (src, trg) = (f srcL src, f trgL trg, n)
    where
    f ∷ Text → Text → Unannotated
    f l = Unannotated.fromText g l

dropRecreateUser ∷ Connection → User → IO ()
dropRecreateUser c User{..}
  = void
  $ Database.runDbT act c
  where
  act ∷ Database.Db ()
  act = do
    Database.rmUser name
    Database.addUser name password enabled

data User = User
  { name     ∷ Text
  , password ∷ Text
  , enabled  ∷ Bool
  }

users ∷ Vector User
users =
  [ User "herbert" "HERBERT" True
  , User "peter"   "PETER"   True
  ]

insertLessonQuery ∷ Query
insertLessonQuery
  = [sql| INSERT INTO Lesson VALUES (?,?,?,?,?,?,?,?,?,?); |]

insertExerciseQuery ∷ Query
insertExerciseQuery
  = [sql|
        INSERT INTO Exercise
        (SourceTree,TargetTree,Lesson)
        VALUES (?,?,?);
    |]
