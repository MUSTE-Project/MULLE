{-# LANGUAGE OverloadedStrings, TypeApplications, LambdaCase #-}
module Database where

import qualified PGF

import Muste

import Database.SQLite.Simple

import Crypto.Random.API

import Crypto.KDF.PBKDF2 hiding (generate)
import Crypto.Hash (Digest(..),SHA3_512(..),hash)

import qualified Data.ByteString as BS
import qualified Data.ByteString.Base64 as B64
import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Lazy.Char8 as LB
import qualified Data.Text as T
import qualified Data.Map.Lazy as M
import Data.Maybe

import Test.QuickCheck

import Data.Time.Clock
import Data.Time.Format

import Control.Exception

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

initContexts :: Connection -> IO (M.Map T.Text (M.Map String Context))
initContexts conn = do
  lessonGrammarList <- query_ conn selectLessonsGrammarsQuery
  grammarList <- mapM readPGF lessonGrammarList
  preTuples <- mapM readLangs grammarList
  pure (M.fromList preTuples)
  where
  selectLessonsGrammarsQuery = "SELECT Name, Grammar FROM Lesson;" :: Query
  selectStartTreesQuery = "SELECT SourceTree FROM Exercise WHERE Lesson = ?;" :: Query
  readPGF (lesson,grammarName) = do
    -- get all langs
    pgf <- PGF.readPGF (T.unpack grammarName)
    pure (lesson,pgfToGrammar pgf)
  readLangs (lesson, grammar) = do
    -- get all langs
    let langs = PGF.languages (pgf grammar)
    -- get all start trees
    let contexts = [(PGF.showCId lang,buildContext grammar lang) | lang <- langs]
    -- precompute for every lang and start tree
    pure (lesson, M.fromList contexts)

createUser
  :: Connection
  -> T.Text -- ^ Username
  -> String -- ^ Password
  -> Bool -- ^ User enabled
  -> IO Types.User
createUser conn user pass enabled =
  do
    -- Create a salted password
    salt <- createSalt
    let safePw = hashPasswd (B.pack pass) salt
    pure (user, safePw, salt, enabled)

addUser
  :: Connection
  -> T.Text -- ^ Username
  -> String -- ^ Password
  -> Bool -- ^ User enabled
  -> IO ()
addUser conn user pass enabled = do
  u <- createUser conn user pass enabled
  -- Remove user if they already exists
  let deleteQuery = "DELETE FROM User WHERE Username = ?;" :: Query
  execute conn deleteQuery [user]
  -- Add new user
  let insertQuery = "INSERT INTO User VALUES (?,?,?,?);" :: Query
  execute conn insertQuery u

authUser
  :: Connection
  -> T.Text -- ^ Username
  -> String -- ^ Password
  -> IO Bool
authUser conn user pass =
  do
    -- Get password and salt from database
    let selectPasswordSaltQuery = "SELECT Password,Salt,Enabled FROM User WHERE (Username = ?);" :: Query
    userList <- (query conn selectPasswordSaltQuery [user]) :: IO [(B.ByteString,B.ByteString,Bool)]
    -- Generate new password hash and compare to the stored one
    if length userList == 1 then
      let (dbPass,dbSalt,enabled) = head userList
          pwHash = hashPasswd (B.pack pass) dbSalt
      in return $ enabled && pwHash == dbPass
      else
      return False

changePassword
  :: Connection
  -> T.Text -- ^ Username
  -> String -- ^ Old password
  -> String -- ^ New password
  -> IO ()
changePassword conn user oldPass newPass =
  do
    authed <- authUser conn user oldPass
    if authed
    then addUser conn user newPass True
    else return ()

createSession
  :: Connection
  -> T.Text -- ^ Username
  -> IO Types.Session
createSession conn user = do
    -- maybe check for old sessions and clean up?
    let deleteSessionQuery = "DELETE FROM Session WHERE User = ? ;" :: Query
    execute conn deleteSessionQuery [user]
    -- create new session
    timeStamp <- getCurrentTime
    let sessionData
         = T.unpack user
         <> formatTime defaultTimeLocale "%s" timeStamp

    let token :: T.Text
        token = T.pack (show (hash (B.pack sessionData) :: Digest SHA3_512) :: String)
    pure (user, token, timeStamp, timeStamp)

-- | Creates a new session and returns the session token.  At the
-- moment overly simplified.
startSession
  :: Connection
  -> T.Text -- ^ Username
  -> IO T.Text
startSession conn user = do
  session@(_, token, _, _) <- createSession conn user
  let insertSessionQuery = "INSERT INTO Session VALUES (?,?,?,?);" :: Query
  execute conn insertSessionQuery session
  return token

updateActivity :: Connection -> String -> IO ()
updateActivity conn token =
  do
    timeStamp <- formatTime defaultTimeLocale "%s" <$> getCurrentTime
    let updateSessionLastActiveQuery = "UPDATE Session SET LastActive = ? WHERE Token = ?;" :: Query
    execute conn updateSessionLastActiveQuery (timeStamp,token)

-- | Returns @Just err@ if there is an error.
verifySession
  :: Connection
  -> String -- ^ Token
  -> IO (Maybe String)
verifySession conn token = do
  -- Get potential user session(s)
  let selectSessionQuery = "SELECT LastActive FROM Session WHERE Token = ?;" :: Query
  sessions <- query conn selectSessionQuery [token] :: IO [Only UTCTime]
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
    execute conn deleteSessionQuery [token]
    pure $ pure error

-- | List all the lessons i.e. lesson name, description and exercise count
listLessons
  :: Connection
  -> T.Text -- Token
  -> IO [(String,String,Int,Int,Int,Int,Bool,Bool)]
listLessons conn token = do
  let qry :: (ToRow q, FromRow r) => Query -> q -> IO [r]
      qry = query conn
  users <- qry @(Only T.Text) @(Only T.Text) "SELECT User FROM Session WHERE Token = ?;" (Only token)
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
    [Only user] -> query conn listLessonsQuery [user]
    usrs      -> throw $ DatabaseException "Non unique user associated with token"

-- | Start a new lesson by randomly choosing the right number of
-- exercises and adding them to the users exercise list
startLesson
  :: Connection
  -> String -- ^ Token
  -> T.Text -- ^ Lesson name
  -> IO (String,String,String,String)
startLesson conn token lesson = do
  -- get user name
  Only user <- fromMaybe errUsr . listToMaybe
    <$> query conn userQuery (Only token)
  isRunning <- (0 /=) . fromOnly . head
    <$> (query conn checkLessonStartedQuery [user,lesson] :: IO [Only Int])
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
  -> T.Text -- ^ Username
  -> T.Text -- ^ Lesson name
  -> IO (String,String,String,String)
newLesson conn user lesson = do
  -- get exercise count
  Only count <- fromMaybe errNonUniqueLesson . listToMaybe
    -- (\case { [Only count] -> count ; _ -> error "Database.newLesson: Non unique lesson"})
    <$> query conn exerciseCountQuery (Only lesson)
  -- get lesson round
  [[round]] <- query conn lessonRoundQuery [user,lesson]
  -- get all exercises for lesson
  trees <- query conn exerciseQuery [lesson] :: IO [(String,String)]
  -- randomly select
  selectedTrees <- fmap (take count) $ generate $ shuffle trees
  let (sourceTree,targetTree) = fromMaybe errNoExercises $ listToMaybe $ selectedTrees
  -- save in database
  let startedLesson :: Types.StartedLesson
      startedLesson = (lesson, user, succ round)
  execute conn insertStartedLesson startedLesson
  mapM_ (\(sTree,tTree) -> execute conn insertExerciseList (lesson,user,sTree,tTree,round)) selectedTrees
  -- get languages
  let languagesQuery = "SELECT SourceLanguage, TargetLanguage FROM Lesson WHERE Name = ?;" :: Query
  langs <- query conn languagesQuery [lesson] :: IO [(String,String)]
  if length langs == 1
  then
    let (sourceLang,targetLang) = head langs
    in return (sourceLang,sourceTree,targetLang,targetTree)
  else
      throw $ DatabaseException "Couldn't find the languages"
  where
  exerciseCountQuery = "SELECT ExerciseCount FROM Lesson WHERE Name = ?;"
  lessonRoundQuery = "SELECT ifnull(MAX(Round),0) FROM FinishedExercise WHERE User = ? AND Lesson = ?;"
  exerciseQuery = "SELECT SourceTree,TargetTree FROM Exercise WHERE Lesson = ?;"
  insertStartedLesson = "INSERT INTO StartedLesson (Lesson, User, Round) VALUES (?,?,?);"
  insertExerciseList = "INSERT INTO ExerciseList (Lesson,User,SourceTree,TargetTree,Round) VALUES (?,?,?,?,?);"
  errNoExercises = error "Database.newLesson: Invariant violated: No exercises for lesson"
  errNonUniqueLesson = error "Database.newLesson: Non unique lesson"

continueLesson
  :: Connection
  -> T.Text -- ^ Username
  -> T.Text -- ^ Lesson name
  -> IO (String,String,String,String)
continueLesson conn user lesson = do
  [Only round] <- query @_ @(Only Integer)
    conn lessonRoundQuery (user,lesson)
  (sourceTree,targetTree) <- fromMaybe errNoExercises . listToMaybe
    <$> query conn selectExerciseListQuery (lesson,user,round)
  [(sourceLang,targetLang)] <- query conn languagesQuery (Only lesson)
  return (sourceLang,sourceTree,targetLang,targetTree)
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

finishExercise
  :: Connection
  -> String -- ^ Token
  -> T.Text -- ^ Lesson
  -> Int -- ^ Time
  -> Integer -- ^ Clicks
  -> IO ()
finishExercise conn token lesson time clicks = do
  -- get user name
  [[user]] <- query conn userQuery [token] :: IO [[String]]
  -- get lesson round
  [Only round] <- query @_ @(Only Integer) conn lessonRoundQuery (user,lesson)
  ((sourceTree,targetTree):_) <- query conn selectExerciseListQuery (lesson,user,round) :: IO [(String,String)]
  execute conn insertFinishedExerciseQuery (user, lesson, sourceTree, targetTree, time, clicks + 1, round)
  -- check if all exercises finished
  [Only finishedCount] <- query @_ @(Only Integer) conn countFinishesExercisesQuery (user,lesson)
  [Only exerciseCount] <- query @_ @(Only Integer) conn countExercisesInLesson (Only lesson)
  if finishedCount >= exerciseCount
  then do
    execute conn insertFinishedLessonQuery (user,lesson)
    execute conn deleteStartedLessonQuery (user,lesson)
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
    execute conn deleteSessionQuery [token]
