{-# Language
    OverloadedStrings
  , TypeApplications
  , LambdaCase
  , FlexibleContexts
  , ConstraintKinds
  , CPP
#-}
module Database
  ( getLessons
  , authUser
  , startSession
  , listLessons
  , startLesson
  , finishExercise
  , endSession
  , verifySession
  , addUser
  ) where

import Database.SQLite.Simple
  ( Query, Connection, Only(Only), fromOnly
  , ToRow, FromRow
  )
import qualified Database.SQLite.Simple as SQL (query, query_, execute)

import Crypto.Random.API (getSystemRandomGen, genRandomBytes)
import Crypto.KDF.PBKDF2 (fastPBKDF2_SHA512, Parameters(Parameters))
import Crypto.Hash (Digest(..),SHA3_512(..),hash)

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as M
import Data.Maybe
import Data.Time.Clock
import Data.Time.Format
import Control.Monad.Reader
#if MIN_VERSION_base(4,11,0)
#else
import Data.Semigroup ((<>))
#endif

-- FIXME QuickCheck seems like a heavy dependency just to get access
-- to `shuffle`.
import qualified Test.QuickCheck as QC (shuffle, generate)

import Control.Exception
import Control.Monad.IO.Class

import qualified Database.Types as Types

-- TODO User transactions for most of these methods.

data DatabaseException = DatabaseException String deriving (Show)
instance Exception DatabaseException

-- | hashPasswd returns a SHA512 hash of a PBKDF2 encoded password
-- (SHA512,10000 iterations,1024 bytes output)
hashPasswd :: B.ByteString -> B.ByteString -> BS.ByteString
hashPasswd = fastPBKDF2_SHA512
  (Parameters 10000 1024)

-- | createSalt returns a SHA512 hash of 512 bytes of random data as a
-- bytestring
createSalt :: IO B.ByteString
createSalt = do
  rng <- getSystemRandomGen
  return $ fst $ genRandomBytes 512 rng

getLessons
  :: MonadIO io
  => Connection
  -> io [Types.Lesson]
getLessons conn = liftIO $ SQL.query_ conn "select * from lesson;"

createUser
  :: Connection
  -> Text -- ^ Username
  -> Text -- ^ Password
  -> Bool -- ^ User enabled
  -> IO Types.User
createUser conn user pass enabled = do
  -- Create a salted password
  salt <- createSalt
  let safePw = hashPasswd (T.encodeUtf8 pass) salt
  pure (user, safePw, salt, enabled)

addUser
  :: Connection
  -> Text -- ^ Username
  -> Text -- ^ Password
  -> Bool -- ^ User enabled
  -> IO ()
addUser conn user pass enabled = do
  u <- createUser conn user pass enabled
  -- Remove user if they already exists
  let deleteQuery = "DELETE FROM User WHERE Username = ?;" :: Query
  SQL.execute conn deleteQuery [user]
  -- Add new user
  let insertQuery = "INSERT INTO User VALUES (?,?,?,?);" :: Query
  SQL.execute conn insertQuery u

authUser
  :: MonadIO io
  => Connection
  -> Text -- ^ Username
  -> Text -- ^ Password
  -> io Bool
authUser conn user pass = liftIO $ do
  -- Get password and salt from database
  userList <- (SQL.query conn selectPasswordSaltQuery [user]) :: IO [(B.ByteString,B.ByteString,Bool)]
  -- Generate new password hash and compare to the stored one
  if length userList == 1
  then
    let (dbPass,dbSalt,enabled) = head userList
        pwHash = hashPasswd (T.encodeUtf8 pass) dbSalt
    in pure $ enabled && pwHash == dbPass
  else pure False
  where
  selectPasswordSaltQuery
    = "SELECT Password,Salt,Enabled FROM User WHERE (Username = ?);"

changePassword
  :: Connection
  -> Text -- ^ Username
  -> Text -- ^ Old password
  -> Text -- ^ New password
  -> IO ()
changePassword conn user oldPass newPass =
  do
    authed <- authUser conn user oldPass
    if authed
    then addUser conn user newPass True
    else return ()

createSession
  :: Connection
  -> Text -- ^ Username
  -> IO Types.Session
createSession conn user = do
    -- maybe check for old sessions and clean up?
    let deleteSessionQuery = "DELETE FROM Session WHERE User = ? ;" :: Query
    SQL.execute conn deleteSessionQuery [user]
    -- create new session
    timeStamp <- getCurrentTime
    let sessionData
         = T.unpack user
         <> formatTime defaultTimeLocale "%s" timeStamp

    let token :: Text
        token = T.pack (show (hash (B.pack sessionData) :: Digest SHA3_512) :: String)
    pure (user, token, timeStamp, timeStamp)

-- | Creates a new session and returns the session token.  At the
-- moment overly simplified.
startSession
  :: MonadIO io
  => Connection
  -> Text -- ^ Username
  -> io Text
startSession conn user = liftIO $ do
  session@(_, token, _, _) <- createSession conn user
  let insertSessionQuery = "INSERT INTO Session VALUES (?,?,?,?);" :: Query
  SQL.execute conn insertSessionQuery session
  return token

updateActivity :: Connection -> String -> IO ()
updateActivity conn token =
  do
    timeStamp <- formatTime defaultTimeLocale "%s" <$> getCurrentTime
    let updateSessionLastActiveQuery = "UPDATE Session SET LastActive = ? WHERE Token = ?;" :: Query
    SQL.execute conn updateSessionLastActiveQuery (timeStamp,token)

-- | Returns @Just err@ if there is an error.
verifySession
  :: Connection
  -> String -- ^ Token
  -> IO (Maybe String)
verifySession conn token = do
  -- Get potential user session(s)
  let selectSessionQuery = "SELECT LastActive FROM Session WHERE Token = ?;" :: Query
  sessions <- SQL.query conn selectSessionQuery [token] :: IO [Only UTCTime]
  -- from here might not be executed due to lazy evaluation...
  -- Compute the difference in time stamps
  newTimeStamp <- getCurrentTime
  let oldTimeStamp = fromOnly . head $ sessions
      deleteSessionQuery = "DELETE FROM Session WHERE Token = ? ;"
      diff = diffUTCTime newTimeStamp oldTimeStamp
      hour = fromInteger 60
      threshold = fromInteger (30 * hour)
      error
        | length sessions  == 0 = "Not current session"
        | diff > threshold      = "Session timeout"
        | otherwise             = "More than one session"
  -- ... until here. check if a session exists and it is has been active in the last 30 minutes
  if length sessions == 1 && diff <= threshold
  then pure Nothing
  else do
    SQL.execute conn deleteSessionQuery [token]
    pure $ pure error

-- | List all the lessons i.e. lesson name, description and exercise
-- count
listLessons
  :: MonadIO io
  => Connection
  -> Text -- Token
  -> io [(Text,Text,Int,Int,Int,NominalDiffTime,Bool,Bool)]
listLessons conn token = liftIO $ do
  let qry :: (ToRow q, FromRow r) => Query -> q -> IO [r]
      qry = SQL.query conn
  users <- qry @(Only Text) @(Only Text) "SELECT User FROM Session WHERE Token = ?;" (Only token)
  let listLessonsQuery = mconcat
       [ "WITH userName AS (SELECT ?), "
       , "maxRounds AS (SELECT Lesson,IFNULL(MAX(Round),0) AS Round FROM "
       , "    (SELECT * FROM StartedLesson UNION SELECT Lesson,User,Round FROM FinishedLesson) "
       , "WHERE User = (SELECT * FROM userName) GROUP BY Lesson) "
       , "SELECT Name, Description, ExerciseCount,"
       , "(SELECT COUNT(*) AS Passed FROM FinishedExercise WHERE "
       , "User = (SELECT * FROM userName) AND Lesson = Name AND Round = "
       , "    (SELECT Round FROM maxRounds WHERE User = (SELECT * FROM userName) AND Lesson = Name)"
       , ") AS Passed, "
       , "(SELECT IFNULL(SUM(ClickCount),0) FROM FinishedExercise F WHERE "
       , "User = (SELECT * from UserName) AND Lesson = Name  AND Round = "
       , "    (SELECT Round FROM maxRounds WHERE User = (SELECT * FROM userName) AND Lesson = Name)"
       , ") AS Score, "
       , "(SELECT IFNULL(SUM(Time),0) FROM FinishedExercise F WHERE "
       , "User = (SELECT * from UserName) AND Lesson = Name  AND Round = "
       , "    (SELECT Round FROM maxRounds WHERE User = (SELECT * FROM userName) AND Lesson = Name)"
       , ") AS Time, "
       , "(SELECT MIN(IFNULL(COUNT(*),0),1) FROM FinishedLesson WHERE "
       , "User = (SELECT * from UserName) AND Lesson = Name) AS Passed, "
       , "Enabled "
       , "FROM Lesson;"
       ]
  case users of
    [] -> throw $ DatabaseException "No user found"
    [Only user] -> SQL.query conn listLessonsQuery [user]
    usrs      -> throw $ DatabaseException "Non unique user associated with token"

-- | Start a new lesson by randomly choosing the right number of
-- exercises and adding them to the users exercise list
startLesson
  :: MonadIO io
  => Connection
  -> String -- ^ Token
  -> Text -- ^ Lesson name
  -- * Source- language and tree, target- langauge and tree.
  -> io (String, Types.TTree, String, Types.TTree)
startLesson conn token lesson = liftIO $ do
  -- get user name
  Only user <- fromMaybe errUsr . listToMaybe
    <$> SQL.query conn userQuery (Only token)
  isRunning <- (0 /=) . fromOnly . head
    <$> (SQL.query conn checkLessonStartedQuery [user,lesson] :: IO [Only Int])
  if isRunning
  then continueLesson conn user lesson
  else newLesson      conn user lesson
  where
  userQuery
    = "SELECT User FROM Session WHERE Token = ?;"
  checkLessonStartedQuery
    = "SELECT COUNT(*) FROM StartedLesson WHERE User = ? AND Lesson = ?"
  errUsr = error "No active session for user"

newLesson
  :: Connection
  -> Text -- ^ Username
  -> Text -- ^ Lesson name
  -> IO ( String, Types.TTree
        , String, Types.TTree
        )
newLesson conn usr lsn = newLessonM usr lsn `runDB` conn

type DB a = ReaderT Connection IO a

type MonadDB m =
  ( MonadReader Connection m
  , MonadIO m
  )

runDB :: DB a -> Connection -> IO a
runDB = runReaderT

liftDB :: MonadDB db => (Connection -> IO a) -> db a
liftDB act = do
  c <- ask
  liftIO (act c)

query
  :: MonadDB db
  => (ToRow q, FromRow r)
  => Query -> q -> db [r]
query qry q = liftDB (\c -> SQL.query c qry q)

execute
  :: MonadDB db
  => ToRow q
  => Query
  -> q
  -> db ()
execute qry q = liftDB (\c -> SQL.execute c qry q)

shuffle :: MonadIO m => [a] -> m [a]
shuffle = liftIO . QC.generate . QC.shuffle

getTreePairs
  :: MonadDB db
  => Text
  -> db [(Types.TTree, Types.TTree)]
getTreePairs lesson = query exerciseQuery (Only lesson)
  where
  exerciseQuery
    =  "SELECT SourceTree, TargetTree "
    <> "FROM Exercise "
    <> "WHERE Lesson = ?;"

newLessonM :: Text -> Text -> DB
  ( String, Types.TTree
  , String, Types.TTree
  )
newLessonM user lesson = do
  -- get exercise count
  count <- fromOnly . fromMaybe errNonUniqueLesson . listToMaybe
    -- (\case { [Only count] -> count ; _ -> error "Database.newLesson: Non unique lesson"})
    <$> query exerciseCountQuery (Only lesson)
  -- get lesson round
  [[round]] <- query lessonRoundQuery [user,lesson]
  trees <- getTreePairs lesson
  -- randomly select
  selectedTrees <- take count <$> shuffle trees
  let (sourceTree,targetTree)
        = fromMaybe errNoExercises $ listToMaybe $ selectedTrees
  -- save in database
  let startedLesson :: Types.StartedLesson
      startedLesson = (lesson, user, succ round)
  execute insertStartedLesson startedLesson
  mapM_ (\(sTree,tTree) -> execute insertExerciseList (lesson,user,sTree,tTree,round)) selectedTrees
  -- get languages
  let languagesQuery = "SELECT SourceLanguage, TargetLanguage FROM Lesson WHERE Name = ?;" :: Query
  langs <- query @_ @_ languagesQuery [lesson] -- :: IO [(String,String)]
  case langs of
    [(sourceLang, targetLang)] -> do
      pure (sourceLang, sourceTree, targetLang, targetTree)
    _ -> throw $ DatabaseException "Couldn't find the languages"
  where
  exerciseCountQuery = "SELECT ExerciseCount FROM Lesson WHERE Name = ?;"
  lessonRoundQuery = "SELECT ifnull(MAX(Round),0) FROM FinishedExercise WHERE User = ? AND Lesson = ?;"
  insertStartedLesson = "INSERT INTO StartedLesson (Lesson, User, Round) VALUES (?,?,?);"
  insertExerciseList = "INSERT INTO ExerciseList (Lesson,User,SourceTree,TargetTree,Round) VALUES (?,?,?,?,?);"
  errNoExercises = error "Database.newLesson: Invariant violated: No exercises for lesson"
  errNonUniqueLesson = error "Database.newLesson: Non unique lesson"

continueLesson
  :: Connection
  -> Text -- ^ Username
  -> Text -- ^ Lesson name
  -> IO
     ( String
     , Types.TTree
     , String
     , Types.TTree
     )
continueLesson conn user lesson = continueLessonM user lesson `runDB` conn

continueLessonM
  :: MonadDB db
  => Text -- ^ Username
  -> Text -- ^ Lesson name
  -> db
    ( String
    , Types.TTree
    , String
    , Types.TTree
    )
continueLessonM user lesson = do
  [Only round] <- query @_ @_ @(Only Integer)
    lessonRoundQuery (user,lesson)
  (sourceTree,targetTree) <- fromMaybe errNoExercises . listToMaybe
    <$> query @_ @_ @(Types.TTree, Types.TTree)
        selectExerciseListQuery (lesson,user,round)
  (sourceLang,targetLang)
    <- fromMaybe errLangs . listToMaybe
    <$> query languagesQuery (Only lesson)
  pure (sourceLang,sourceTree,targetLang,targetTree)
  where
  lessonRoundQuery
    = "SELECT ifnull(MAX(Round),0) FROM FinishedExercise WHERE User = ? AND Lesson = ?;"
  selectExerciseListQuery
    =  "SELECT SourceTree,TargetTree FROM ExerciseList "
    <> "WHERE Lesson = ? AND User = ? "
    <> "AND (User,SourceTree,TargetTree,Lesson) NOT IN "
    <> "(SELECT User,SourceTree,TargetTree,Lesson "
    <> "FROM FinishedExercise WHERE Round = ?);"
  languagesQuery
    = "SELECT SourceLanguage, TargetLanguage FROM Lesson WHERE Name = ?;"
  errNoExercises = error "Database.continueLesson: Invariant violated: No exercises for lesson"
  errLangs = error "Database.continueLesson: Invariant violated: Multiple results for lesson"

finishExercise
  :: Connection
  -> String -- ^ Token
  -> Text -- ^ Lesson
  -> NominalDiffTime -- ^ Time elapsed
  -> Integer -- ^ Clicks
  -> IO ()
finishExercise conn token lesson time clicks = do
  -- get user name
  [[user]] <- SQL.query conn userQuery [token] :: IO [[String]]
  -- get lesson round
  [Only round] <- SQL.query @_ @(Only Integer) conn lessonRoundQuery (user,lesson)
  ((sourceTree,targetTree):_) <- SQL.query conn selectExerciseListQuery (lesson,user,round) :: IO [(String,String)]
  SQL.execute conn insertFinishedExerciseQuery (user, lesson, sourceTree, targetTree, time, clicks + 1, round)
  -- check if all exercises finished
  [Only finishedCount] <- SQL.query @_ @(Only Integer) conn countFinishesExercisesQuery (user,lesson)
  [Only exerciseCount] <- SQL.query @_ @(Only Integer) conn countExercisesInLesson (Only lesson)
  if finishedCount >= exerciseCount
  then do
    SQL.execute conn insertFinishedLessonQuery (user,lesson)
    SQL.execute conn deleteStartedLessonQuery (user,lesson)
  else return ()
  where
    userQuery = "SELECT User FROM Session WHERE Token = ?;"
    lessonRoundQuery = "SELECT ifnull(MAX(Round),1) FROM StartedLesson WHERE User = ? AND Lesson = ?;"
    selectExerciseListQuery = "SELECT SourceTree,TargetTree FROM ExerciseList WHERE Lesson = ? AND User = ? AND (User,SourceTree,TargetTree,Lesson) NOT IN (SELECT User,SourceTree,TargetTree,Lesson FROM FinishedExercise WHERE Round = ?);"
    insertFinishedExerciseQuery = "INSERT INTO FinishedExercise (User,Lesson,SourceTree,TargetTree,Time,ClickCount,Round) VALUES (?,?,?,?,?,?,?);"
    countFinishesExercisesQuery = "SELECT COUNT(*) FROM FinishedExercise F WHERE User = ? AND Lesson = ? AND Round = (SELECT MAX(Round) FROM StartedLesson WHERE User = F.User AND Lesson = F.Lesson);"
    countExercisesInLesson = "SELECT ExerciseCount FROM Lesson WHERE Name = ?;"
    deleteStartedLessonQuery = "DELETE FROM StartedLesson WHERE User = ? AND Lesson = ? ;"
    insertFinishedLessonQuery = mconcat
      [ "WITH userName AS (SELECT ?),"
      , "lessonName AS (SELECT ?),"
      , "roundCount as (SELECT MAX(Round) FROM StartedLesson WHERE User = (SELECT * FROM userName) AND Lesson = (SELECT * FROM lessonName)) "
      , "INSERT INTO FinishedLesson (User,Lesson,Time,ClickCount,Round) VALUES "
      , "((SELECT * FROM userName),"
      , "(SELECT * FROM lessonName),"
      , "(SELECT SUM(Time) FROM FinishedExercise WHERE User = (SELECT * FROM userName) AND Lesson = (SELECT * FROM lessonName) AND Round = (SELECT * FROM roundCount)),"
      , "(SELECT SUM(clickcount) FROM FinishedExercise WHERE User = (SELECT * FROM userName) AND Lesson = (SELECT * FROM lessonName) AND Round = (SELECT * FROM roundCount)),"
      , "(SELECT * FROM roundCount));"
      ]

endSession :: Connection -> String -> IO ()
endSession conn token =
  do
    let deleteSessionQuery = "DELETE FROM Session WHERE Token = ?;"
    SQL.execute conn deleteSessionQuery [token]
