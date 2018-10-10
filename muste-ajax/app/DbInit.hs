{-# LANGUAGE OverloadedStrings, UnicodeSyntax, TemplateHaskell,
  QuasiQuotes, TypeApplications, RecordWildCards, OverloadedLists #-}
{-# OPTIONS_GHC -Wall #-}
module DbInit (initDb) where

import           Prelude ()
import           Muste.Prelude
import           Muste.Prelude.SQL (Connection(Connection), Query, sql)
import qualified Muste.Prelude.SQL as SQL

import           Data.ByteString (ByteString)
import           Data.FileEmbed (embedFile, makeRelativeToProject)
import           Data.Text.Encoding (decodeUtf8)
import qualified Database.SQLite3 as SQL
import           System.Directory (createDirectoryIfMissing)
import           System.FilePath (takeDirectory)
import qualified Data.Yaml as Yaml

import           Muste.Sentence.Unannotated (Unannotated)
import qualified Muste.Sentence.Unannotated as Unannotated

import qualified Muste.Web.Config         as Config
import qualified Muste.Web.Database       as Database
import qualified Muste.Web.Database.Types as Database

import qualified DbInit.Data as Data

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
  execRaw conn $ decodeUtf8 initScript
  mapM_ (dropRecreateUser conn) Config.users
  lessons ← Yaml.decodeFileThrow Config.lessons
  SQL.executeMany @Database.Lesson conn insertLessonQuery
    $ toDatabaseLesson <$> lessons
  SQL.executeMany @Database.Exercise conn insertExerciseQuery
    $ lessons >>= toDatabaseExercise

-- | Converts our nested structure from the config file to something
-- suitable for a RDBMS.
toDatabaseLesson ∷ Data.Lesson → Database.Lesson
toDatabaseLesson Data.Lesson{..}
  = Database.Lesson
  { name                = name
  , description         = description
  , grammar             = grammar
  , sourceLanguage      = sourceLanguage
  , targetLanguage      = targetLanguage
  , exerciseCount       = toInteger $ length exercises'
  , enabled             = enabled
  , searchLimitDepth    = searchDepthLimit
  , searchLimitSize     = searchSizeLimit
  , repeatable          = repeatable
  }
  where
  Data.LessonSettings{..} = settings
  Data.Languages sourceLanguage targetLanguage = languages
  Data.SearchOptions{..} = searchOptions

toDatabaseExercise ∷ Data.Lesson → [Database.Exercise]
toDatabaseExercise Data.Lesson{..} = step <$> exercises'
  where
  step Data.Exercise{..}
    = Database.Exercise
    { sourceLinearization = lin srcL source
    , targetLinearization = lin trgL target
    , lesson              = name
    , timeout             = 0
    }
  Data.LessonSettings{..} = settings
  Data.Languages srcL trgL = languages
  lin ∷ Text → Data.Sentence → Unannotated
  lin l (Data.Sentence t) = Unannotated.fromText grammar l t

dropRecreateUser ∷ Connection → Config.User → IO ()
dropRecreateUser c Config.User{..}
  = void
  $ Database.runDbT act c
  where
  name' = convertString name
  password' = convertString password
  act ∷ Database.Db ()
  act = do
    Database.rmUser  name'
    Database.addUser name' password' enabled

insertLessonQuery ∷ Query
insertLessonQuery
  = [sql| INSERT INTO Lesson VALUES (?,?,?,?,?,?,?,?,?,?); |]

insertExerciseQuery ∷ Query
insertExerciseQuery
  = [sql|
        INSERT INTO Exercise
        (SourceTree,TargetTree,Lesson,Timeout)
        VALUES (?,?,?,?);
    |]
