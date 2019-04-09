{-# OPTIONS_GHC -Wall #-}
{-# Language
 CPP,
 LambdaCase,
 OverloadedLists,
 OverloadedStrings,
 QuasiQuotes,
 RecordWildCards,
 TemplateHaskell,
 TypeApplications
#-}

module Muste.Web.DbInit (initDb) where

import           Prelude ()
import           Muste.Prelude

import           Database.SQLite.Simple (Connection(Connection))
import           Database.SQLite.Simple.QQ (sql)
import qualified Database.SQLite.Simple as SQL

import           Data.ByteString (ByteString)
import           Data.FileEmbed (embedFile, makeRelativeToProject)
import           Data.Text (pack, unpack)
import           Data.Text.Encoding (decodeUtf8)
import qualified Database.SQLite3 as SQL
import           System.Directory (createDirectoryIfMissing)
import           System.FilePath (takeDirectory, (</>))
import qualified Data.Yaml as Yaml

#ifdef DIAGNOSTICS
import qualified Data.Text.IO as Text
#endif

import           Muste.Sentence.Unannotated (Unannotated)
import qualified Muste.Sentence.Unannotated as Unannotated

import qualified Muste.Web.Config         as Config
import qualified Muste.Web.Database       as Database
import qualified Muste.Web.Database.Types as Database
import qualified Muste.Web.DbInit.Data    as Data

initDb :: Config.AppConfig -> IO ()
initDb cfg = do
  putStrLn "[Initializing database...]"
  mkParDir (Config.db cfg)
  withConnection (Config.db cfg) (initDbAux cfg)
  putStrLn "[Initializing database... Done]"

withConnection :: FilePath -> (Connection -> IO ()) -> IO ()
withConnection db m =
  SQL.withConnection db $ \c -> do
#ifdef DIAGNOSTICS
    SQL.setTrace c (Just Text.putStrLn)
#endif
    m c

-- | @'mkParDir' p@ Ensure that the directory that @p@ is in is
-- created like the linux command @mkdir -p@.
mkParDir :: FilePath -> IO ()
mkParDir = createDirectoryIfMissing True . takeDirectory

initScript :: ByteString
initScript = $(makeRelativeToProject "data/sql/create.sql" >>= embedFile)

seedScript :: ByteString
seedScript = $(makeRelativeToProject "data/sql/seed.sql" >>= embedFile)

execRaw :: Connection -> Text -> IO ()
execRaw (Connection db) qry = SQL.exec db qry

initDbAux :: Config.AppConfig -> Connection -> IO ()
initDbAux cfg conn = do
  void $ traverse @[] go [ initScript, seedScript ]
  mapM_ (dropRecreateUser conn) (Config.users cfg)
  let lessonsFile = Config.lessons cfg
  lessons' <- Yaml.decodeFileThrow lessonsFile
  let lessonsDir = takeDirectory lessonsFile
  let lessons = [ lesson { Data.grammar = pack (lessonsDir </> unpack grammar) }
                | lesson@Data.Lesson{..} <- lessons'
                ]
  showLessons lessonsFile lessons
  insertLessons conn   $ toDatabaseLesson <$> lessons
  insertExercises conn $ lessons >>= toDatabaseExercise
  where
  go :: ByteString -> IO ()
  go = execRaw conn . decodeUtf8

showLessons :: FilePath -> [Data.Lesson] -> IO ()
showLessons lessonsFile lessons =
  do printf "[Reading lessons file: %s]\n\n" lessonsFile
     mapM_ showLess (zip [1..] lessons)
  where showLess :: (Int, Data.Lesson) -> IO ()
        showLess (n, lesson) =
          printf "[%d: %s = %d exercises]\n" n (Data.name lesson) (length (Data.exercises' lesson))

-- | Converts our nested structure from the config file to something
-- suitable for a RDBMS.
toDatabaseLesson :: Data.Lesson -> Database.Lesson
toDatabaseLesson Data.Lesson{..}
  = Database.Lesson
  { key                 = key
  , name                = name
  , grammar             = grammar
  , sourceLanguage      = sourceLanguage
  , targetLanguage      = targetLanguage
  , exerciseCount       = fromIntegral $ fromMaybe (length exercises') exerciseCount
  , enabled             = enabled
  , searchLimitDepth    = fromIntegral <$> searchDepthLimit
  , searchLimitSize     = fromIntegral <$> searchSizeLimit
  , repeatable          = repeatable
  , sourceDirection     = dir srcDir
  , targetDirection     = dir trgDir
  , highlightMatches    = highlightMatches
  , showSourceSentence  = showSourceSentence
  , randomizeOrder      = randomizeOrder
  }
  where
  Data.LessonSettings{..} = settings
  Data.Languages sourceLanguage targetLanguage = languages
  Data.SearchOptions{..} = searchOptions
  dir :: Data.Direction -> Database.Direction
  dir = \case
    Data.VersoRecto -> Database.VersoRecto
    Data.RectoVerso -> Database.RectoVerso

toDatabaseExercise :: Data.Lesson -> [Database.Exercise]
toDatabaseExercise Data.Lesson{..} = step <$> zip [0..] exercises'
  where
  step (n, Data.Exercise{..})
    = Database.Exercise
    { sourceLinearization = lin srcL source
    , targetLinearization = lin trgL target
    , lesson              = key
    , timeout             = 0
    , exerciseOrder       = n
    }
  Data.LessonSettings{..} = settings
  Data.Languages srcL trgL = languages
  lin :: Text -> Data.Sentence -> Unannotated
  lin l (Data.Sentence t) = Unannotated.fromText grammar l t

dropRecreateUser :: Connection -> Config.User -> IO ()
dropRecreateUser c Config.User{..}
  = void
  $ flip Database.runDbT c
  $ Database.addUser
  $ Database.CreateUser
    { name     = convertString name
    , password = convertString password
    , enabled  = enabled
    }

insertLessons :: Connection -> [Database.Lesson] -> IO ()
insertLessons c = SQL.executeMany c q
  where

  q = [sql|
-- insertLessons
INSERT INTO Lesson
( Id
, Name
, Grammar
, SourceLanguage
, TargetLanguage
, ExerciseCount
, Enabled
, SearchLimitDepth
, SearchLimitSize
, Repeatable
, SourceDirection
, TargetDirection
, HighlightMatches
, ShowSourceSentence
, RandomizeOrder
)
VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
;|]

insertExercises :: Connection -> [Database.Exercise] -> IO ()
insertExercises c = SQL.executeMany c q
  where

  q = [sql|
-- insertExercises
INSERT INTO Exercise
( SourceTree
, TargetTree
, Lesson
, Timeout
, ExerciseOrder
)
VALUES (?,?,?,?,?);
|]
