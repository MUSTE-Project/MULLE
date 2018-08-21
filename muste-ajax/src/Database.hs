-- TODO Fix name shadowing.
{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
{-# Language CPP, QuasiQuotes #-}
module Database
  ( MonadDB
  , DB
  , HasConnection(getConnection)
  , runDB
  , getLessons
  , authUser
  , startSession
  , listLessons
  , startLesson
  , finishExercise
  , endSession
  , verifySession
  , addUser
  , changePassword
  , updateActivity
  ) where

import Database.SQLite.Simple
  ( Query, Connection, Only(Only), fromOnly
  , ToRow, FromRow
  )
import Database.SQLite.Simple.QQ (sql)
import qualified Database.SQLite.Simple as SQL (query, query_, execute)

import Crypto.Random.API (getSystemRandomGen, genRandomBytes)
import Crypto.KDF.PBKDF2 (fastPBKDF2_SHA512, Parameters(Parameters))
import Crypto.Hash (Digest,SHA3_512(..),hash)

import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as Char8
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Data.Maybe
import Data.Time.Clock (NominalDiffTime, UTCTime)
import qualified Data.Time.Clock as Time
import Data.Time.Format
import Control.Monad.Reader
#if !(MIN_VERSION_base(4,11,0))
import Data.Semigroup ((<>))
#endif

-- FIXME QuickCheck seems like a heavy dependency just to get access
-- to `shuffle`.
import qualified Test.QuickCheck as QC (shuffle, generate)

import Control.Exception

import qualified Database.Types as Types

data DatabaseException
  = NoUserFound
  | NonUniqueUser
  | LangNotFound

instance Show DatabaseException where
  show = \case
    NoUserFound   → "No user found"
    NonUniqueUser → "Non unique user associated with token"
    LangNotFound  → "Couldn't find the languages"

instance Exception DatabaseException

-- | hashPasswd returns a SHA512 hash of a PBKDF2 encoded password
-- (SHA512,10000 iterations,1024 bytes output)
hashPasswd :: ByteString -> ByteString -> ByteString
hashPasswd = fastPBKDF2_SHA512
  (Parameters 10000 1024)

-- | createSalt returns a SHA512 hash of 512 bytes of random data as a
-- bytestring
createSalt :: MonadIO io ⇒ io ByteString
createSalt = fst . genRandomBytes 512 <$> liftIO getSystemRandomGen

getCurrentTime ∷ MonadIO io ⇒ io UTCTime
getCurrentTime = liftIO Time.getCurrentTime

getLessons
  :: MonadDB db
  => db [Types.Lesson]
getLessons = query_ [sql|select * from lesson;|]

createUser
  :: MonadDB db
  => Text -- ^ Username
  -> Text -- ^ Password
  -> Bool -- ^ User enabled
  -> db Types.User
createUser user pass enabled = do
  -- Create a salted password
  salt <- createSalt
  let safePw = hashPasswd (T.encodeUtf8 pass) salt
  pure (user, safePw, salt, enabled)

addUser
  :: MonadDB db
  => Text -- ^ Username
  -> Text -- ^ Password
  -> Bool -- ^ User enabled
  -> db ()
addUser user pass enabled = do
  u <- createUser user pass enabled
  -- Remove user if they already exists
  let deleteQuery = [sql|DELETE FROM User WHERE Username = ?;|] :: Query
  execute deleteQuery [user]
  -- Add new user
  let insertQuery = [sql|INSERT INTO User VALUES (?,?,?,?);|] :: Query
  execute insertQuery u

authUser
  :: MonadDB db
  => Text -- ^ Username
  -> Text -- ^ Password
  -> db Bool
authUser user pass = do
  -- Get password and salt from database
  userList <- query @(ByteString, ByteString, Bool) selectPasswordSaltQuery [user]
  -- Generate new password hash and compare to the stored one
  if length userList == 1
  then
    let (dbPass,dbSalt,enabled) = head userList
        pwHash = hashPasswd (T.encodeUtf8 pass) dbSalt
    in pure $ enabled && pwHash == dbPass
  else pure False
  where
  selectPasswordSaltQuery
    = [sql|SELECT Password,Salt,Enabled FROM User WHERE (Username = ?);|]

changePassword
  :: MonadDB db
  => Text -- ^ Username
  -> Text -- ^ Old password
  -> Text -- ^ New password
  -> db ()
changePassword user oldPass newPass = do
    authed <- authUser user oldPass
    if authed
    then addUser user newPass True
    else return ()

createSession
  :: MonadDB db
  => Text -- ^ Username
  -> db Types.Session
createSession user = do
    -- maybe check for old sessions and clean up?
    let deleteSessionQuery = [sql|DELETE FROM Session WHERE User = ? ;|] :: Query
    execute deleteSessionQuery [user]
    -- create new session
    timeStamp <- getCurrentTime
    let sessionData
         = T.unpack user
         <> formatTime defaultTimeLocale "%s" timeStamp

    let token :: Text
        token = T.pack (show (hash (Char8.pack sessionData) :: Digest SHA3_512) :: String)
    pure (user, token, timeStamp, timeStamp)

-- | Creates a new session and returns the session token.  At the
-- moment overly simplified.
startSession
  :: MonadDB db
  => Text -- ^ Username
  -> db Text
startSession user = do
  session@(_, token, _, _) <- createSession user
  let insertSessionQuery = [sql|INSERT INTO Session VALUES (?,?,?,?);|] :: Query
  execute insertSessionQuery session
  return token

updateActivity :: MonadDB db ⇒ String -> db ()
updateActivity token = do
  timeStamp <- formatTime defaultTimeLocale "%s" <$> getCurrentTime
  let updateSessionLastActiveQuery = [sql|UPDATE Session SET LastActive = ? WHERE Token = ?;|] :: Query
  execute updateSessionLastActiveQuery (timeStamp,token)

-- | Returns @Just err@ if there is an error.
verifySession
  :: MonadDB db
  => String -- ^ Token
  -> db (Maybe String)
verifySession token = do
  -- Get potential user session(s)
  let selectSessionQuery = [sql|SELECT LastActive FROM Session WHERE Token = ?;|]
  sessions <- query @(Only UTCTime) selectSessionQuery [token]
  -- from here might not be executed due to lazy evaluation...
  -- Compute the difference in time stamps
  newTimeStamp <- getCurrentTime
  let oldTimeStamp = fromOnly . head $ sessions
      deleteSessionQuery = [sql|DELETE FROM Session WHERE Token = ? ;|]
      diff = Time.diffUTCTime newTimeStamp oldTimeStamp
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
    execute deleteSessionQuery [token]
    pure $ pure error

-- | List all the lessons i.e. lesson name, description and exercise
-- count
listLessons
  :: MonadDB db
  => Text -- Token
  -> db [(Text,Text,Int,Int,Int,NominalDiffTime,Bool,Bool)]
listLessons token = do
  users <- query @(Only Text) [sql|SELECT User FROM Session WHERE Token = ?;|] (Only token)
  let listLessonsQuery = [sql|
      WITH userName AS (SELECT ?),
      maxRounds AS (SELECT Lesson,IFNULL(MAX(Round),0) AS Round FROM
          (SELECT * FROM StartedLesson UNION SELECT Lesson,User,Round FROM FinishedLesson)
      WHERE User = (SELECT * FROM userName) GROUP BY Lesson)
      SELECT Name, Description, ExerciseCount,
      (SELECT COUNT(*) AS Passed FROM FinishedExercise WHERE
      User = (SELECT * FROM userName) AND Lesson = Name AND Round =
          (SELECT Round FROM maxRounds WHERE User = (SELECT * FROM userName) AND Lesson = Name)
      ) AS Passed,
      (SELECT IFNULL(SUM(ClickCount),0) FROM FinishedExercise F WHERE
      User = (SELECT * from UserName) AND Lesson = Name  AND Round =
          (SELECT Round FROM maxRounds WHERE User = (SELECT * FROM userName) AND Lesson = Name)
      ) AS Score,
      (SELECT IFNULL(SUM(Time),0) FROM FinishedExercise F WHERE
      User = (SELECT * from UserName) AND Lesson = Name  AND Round =
          (SELECT Round FROM maxRounds WHERE User = (SELECT * FROM userName) AND Lesson = Name)
      ) AS Time,
      (SELECT MIN(IFNULL(COUNT(*),0),1) FROM FinishedLesson WHERE
      User = (SELECT * from UserName) AND Lesson = Name) AS Passed,
      Enabled
      FROM Lesson;|]
  case users of
    []          -> throw NoUserFound
    [Only user] -> query listLessonsQuery [user]
    _usrs       -> throw NonUniqueUser

-- | Start a new lesson by randomly choosing the right number of
-- exercises and adding them to the users exercise list
startLesson
  :: MonadDB db
  => String -- ^ Token
  -> Text -- ^ Lesson name
  -- * Source- language and tree, target- langauge and tree.
  -> db (String, Types.Linearization, String, Types.Linearization)
startLesson token lesson = do
  -- get user name
  Only user <- fromMaybe errUsr . listToMaybe
    <$> query userQuery (Only token)
  isRunning <- (0 /=) . fromOnly . head
    <$> (query @(Only Int) checkLessonStartedQuery [user,lesson])
  if isRunning
  then continueLesson user lesson
  else newLesson      user lesson
  where
  userQuery
    = [sql|SELECT User FROM Session WHERE Token = ?;|]
  checkLessonStartedQuery
    = [sql|SELECT COUNT(*) FROM StartedLesson WHERE User = ? AND Lesson = ?|]
  errUsr = error "No active session for user"

class HasConnection m where
  getConnection ∷ m Connection

instance Monad m ⇒ HasConnection (ReaderT Connection m) where
  getConnection = ask

instance HasConnection DB where
  getConnection = DB ask

newtype DB a = DB (ReaderT Connection IO a) deriving
  ( Functor, Applicative, Monad
  , MonadIO
  )

type MonadDB m = (HasConnection m, MonadIO m)

runDB :: DB a -> Connection -> IO a
runDB (DB db) = runReaderT db

query
  :: ∀ r q db . MonadDB db
  => (ToRow q, FromRow r)
  => Query -> q -> db [r]
query qry q = do
  c ← getConnection
  liftIO $ SQL.query c qry q

query_
  :: ∀ r db . MonadDB db
  => FromRow r
  => Query -> db [r]
query_ qry = do
  c ← getConnection
  liftIO $ SQL.query_ c qry

execute
  :: MonadDB db
  => ToRow q
  => Query
  -> q
  -> db ()
execute qry q = do
  c ← getConnection
  liftIO $ SQL.execute c qry q

shuffle :: MonadIO m => [a] -> m [a]
shuffle = liftIO . QC.generate . QC.shuffle

getTreePairs
  :: MonadDB db
  => Text
  -> db [(Types.Linearization, Types.Linearization)]
getTreePairs lesson = query exerciseQuery (Only lesson)
  where
  exerciseQuery =
    [sql| SELECT SourceTree, TargetTree
          FROM Exercise
          WHERE Lesson = ?;|]

newLesson :: MonadDB db ⇒ Text -> Text -> db
  ( String, Types.Linearization
  , String, Types.Linearization
  )
newLesson user lesson = do
  -- get exercise count
  count <- fromOnly . fromMaybe errNonUniqueLesson . listToMaybe
    <$> query exerciseCountQuery (Only lesson)
  -- get lesson round
  [Only round] <- query lessonRoundQuery [user,lesson]
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
  let languagesQuery = [sql|SELECT SourceLanguage, TargetLanguage FROM Lesson WHERE Name = ?;|]
  langs <- query @_ @_ languagesQuery [lesson] -- :: IO [(String,String)]
  case langs of
    [(sourceLang, targetLang)] -> do
      pure (sourceLang, sourceTree, targetLang, targetTree)
    _ -> throw LangNotFound
  where
  exerciseCountQuery  = [sql|SELECT ExerciseCount FROM Lesson WHERE Name = ?;|]
  lessonRoundQuery    = [sql|SELECT ifnull(MAX(Round),0) FROM FinishedExercise WHERE User = ? AND Lesson = ?;|]
  insertStartedLesson = [sql|INSERT INTO StartedLesson (Lesson, User, Round) VALUES (?,?,?);|]
  insertExerciseList  = [sql|INSERT INTO ExerciseList (Lesson,User,SourceTree,TargetTree,Round) VALUES (?,?,?,?,?);|]
  errNoExercises      = error "Database.newLesson: Invariant violated: No exercises for lesson"
  errNonUniqueLesson  = error "Database.newLesson: Non unique lesson"

continueLesson
  :: MonadDB db
  => Text -- ^ Username
  -> Text -- ^ Lesson name
  -> db
    ( String
    , Types.Linearization
    , String
    , Types.Linearization
    )
continueLesson user lesson = do
  [Only round] <- query @(Only Integer)
    lessonRoundQuery (user,lesson)
  (sourceTree,targetTree) <- fromMaybe errNoExercises . listToMaybe
    <$> query @(Types.Linearization, Types.Linearization)
        selectExerciseListQuery (lesson,user,round)
  (sourceLang,targetLang)
    <- fromMaybe errLangs . listToMaybe
    <$> query languagesQuery (Only lesson)
  pure (sourceLang,sourceTree,targetLang,targetTree)
  where
  lessonRoundQuery
    = [sql|SELECT ifnull(MAX(Round),0) FROM FinishedExercise WHERE User = ? AND Lesson = ?;|]
  selectExerciseListQuery = [sql|
       SELECT SourceTree,TargetTree FROM ExerciseList
       WHERE Lesson = ? AND User = ?
       AND (User,SourceTree,TargetTree,Lesson) NOT IN
       (SELECT User,SourceTree,TargetTree,Lesson
       FROM FinishedExercise WHERE Round = ?);|]
  languagesQuery
    = [sql|SELECT SourceLanguage, TargetLanguage FROM Lesson WHERE Name = ?;|]
  errNoExercises = error "Database.continueLesson: Invariant violated: No exercises for lesson"
  errLangs = error "Database.continueLesson: Invariant violated: Multiple results for lesson"

finishExercise
  :: MonadDB db
  => String -- ^ Token
  -> Text -- ^ Lesson
  -> NominalDiffTime -- ^ Time elapsed
  -> Integer -- ^ Clicks
  -> db ()
finishExercise token lesson time clicks = do
  -- get user name
  [Only user] <- query @(Only String) userQuery [token]
  -- get lesson round
  [Only round] <- query @(Only Integer) lessonRoundQuery (user,lesson)
  ((sourceTree,targetTree):_)
    <- query @(String, String) selectExerciseListQuery (lesson,user,round)
  execute insertFinishedExerciseQuery
    (user, lesson, sourceTree, targetTree, time, clicks + 1, round)
  -- check if all exercises finished
  [Only finishedCount] <- query @(Only Integer) countFinishesExercisesQuery (user,lesson)
  [Only exerciseCount] <- query @(Only Integer) countExercisesInLesson (Only lesson)
  if finishedCount >= exerciseCount
  then do
    execute insertFinishedLessonQuery (user,lesson)
    execute deleteStartedLessonQuery (user,lesson)
  else return ()
  where
    userQuery = [sql|SELECT User FROM Session WHERE Token = ?;|]
    lessonRoundQuery = [sql|
      SELECT ifnull(MAX(Round),1)
      FROM StartedLesson
      WHERE User = ? AND Lesson = ?;
      |]
    selectExerciseListQuery = [sql|
      SELECT SourceTree,TargetTree
      FROM ExerciseList
      WHERE Lesson = ? AND User = ? AND
      (User,SourceTree,TargetTree,Lesson) NOT IN
        (SELECT User,SourceTree,TargetTree,Lesson
         FROM FinishedExercise WHERE Round = ?);
      |]
    insertFinishedExerciseQuery = [sql|
      INSERT INTO FinishedExercise
        (User,Lesson,SourceTree,TargetTree,Time,ClickCount,Round)
      VALUES (?,?,?,?,?,?,?);
      |]
    countFinishesExercisesQuery = [sql|
      SELECT COUNT(*)
      FROM FinishedExercise F
      WHERE User = ? AND Lesson = ? AND Round =
        (SELECT MAX(Round)
        FROM StartedLesson
        WHERE User = F.User AND Lesson = F.Lesson);
      |]
    countExercisesInLesson = [sql|
      SELECT ExerciseCount FROM Lesson WHERE Name = ?;
      |]
    deleteStartedLessonQuery = [sql|
      DELETE FROM StartedLesson
      WHERE User = ? AND Lesson = ? ;
      |]
    insertFinishedLessonQuery = [sql|
      WITH userName AS (SELECT ?),
      lessonName AS (SELECT ?),
      roundCount as (SELECT MAX(Round)
      FROM StartedLesson WHERE User = (SELECT * FROM userName) AND Lesson = (SELECT * FROM lessonName))
      INSERT INTO FinishedLesson (User,Lesson,Time,ClickCount,Round) VALUES
      ((SELECT * FROM userName),
      (SELECT * FROM lessonName),
      (SELECT SUM(Time) FROM FinishedExercise WHERE User = (SELECT * FROM userName) AND Lesson = (SELECT * FROM lessonName) AND Round = (SELECT * FROM roundCount)),
      (SELECT SUM(clickcount) FROM FinishedExercise WHERE User = (SELECT * FROM userName) AND Lesson = (SELECT * FROM lessonName) AND Round = (SELECT * FROM roundCount)),
      (SELECT * FROM roundCount));
      |]

endSession :: MonadDB db ⇒ String -> db ()
endSession token = do
  let deleteSessionQuery = [sql|DELETE FROM Session WHERE Token = ?;|]
  execute deleteSessionQuery [token]
