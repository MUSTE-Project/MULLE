{-# LANGUAGE OverloadedStrings #-}
module Database where

import qualified PGF

import Muste hiding (linearizeTree)
import Muste.Grammar
import Muste.Tree

import Database.SQLite.Simple

import Crypto.Random.API

import Crypto.KDF.PBKDF2 hiding (generate)
import Crypto.Hash (Digest(..),SHA3_512(..),hash)

import qualified Data.ByteString.Base64 as B64
import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Lazy.Char8 as LB
import qualified Data.Text as T
import qualified Data.Map.Lazy as M

import Test.QuickCheck

import Data.Time.Clock
import Data.Time.Format

import Control.Exception

data DatabaseException = DatabaseException String deriving (Show)
instance Exception DatabaseException
-- | hashPasswd returns a SHA512 hash of a PBKDF2 encoded password (SHA512,10000 iterations,1024 bytes output)
hashPasswd :: B.ByteString -> B.ByteString -> B.ByteString
hashPasswd pass salt =
--  B64.encode $ fastPBKDF2_SHA512 (Parameters 10000 1024) pass salt
  fastPBKDF2_SHA512 (Parameters 10000 1024) pass salt

-- | createSalt returns a SHA512 hash of 512 bytes of random data as a bytestring 
createSalt :: IO (B.ByteString)
createSalt =
  do
    rng <- getSystemRandomGen
    -- return $ B64.encode $ fst $ genRandomBytes 512 rng
    return $ fst $ genRandomBytes 512 rng

--- Lesson -> Language -> Grammar
initContexts :: Connection -> IO (M.Map String (M.Map String Context))
initContexts conn =
  do
    let selectLessonsGrammarsQuery = "SELECT Name, Grammar FROM Lesson;" :: Query
    let selectStartTreesQuery = "SELECT SourceTree FROM Exercise WHERE Lesson = ?;" :: Query
    lessonGrammarList <- query_ conn selectLessonsGrammarsQuery :: IO [(String,String)]
    grammarList <- sequence $ map (\(lesson,grammarName) -> do
                           -- get all langs
                           pgf <-PGF.readPGF grammarName
                           let grammar = pgfToGrammar pgf
                           return (lesson,grammar)
                           ) lessonGrammarList :: IO [(String,Grammar)]
    preTuples <- sequence $ map (\(lesson,grammar) -> do
            -- get all langs
            let langs = PGF.languages (pgf grammar)
            -- get all start trees
            let contexts = [(PGF.showCId lang,buildContext grammar lang) | lang <- langs]
             -- precompute for every lang and start tree
            return $ (lesson, M.fromList contexts)
        ) grammarList
    return (M.fromList preTuples)

addUser :: Connection -> String -> String -> Int -> IO ()
addUser conn user pass enabled =
  do
    -- Create a salted password
    salt <- createSalt
    let safePw = hashPasswd (B.pack pass) salt
    -- Remove user if they already exists
    let deleteQuery = "DELETE FROM User WHERE Username = ?;" :: Query
    execute conn deleteQuery [user]
    -- Add new user
    let insertQuery = "INSERT INTO User (Username, Password, Salt, Enabled) VALUES (?,?,?,?);" :: Query
    execute conn insertQuery (user,safePw,salt,enabled)

authUser :: Connection -> String -> String -> IO (Bool)
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
changePassword :: Connection -> String -> String -> String -> IO ()
changePassword conn user oldPass newPass =
  do
    authed <- authUser conn user oldPass
    if authed then addUser conn user newPass 1 else return ()
                                                          
-- | Creates a new session. at the moment overly simplified
startSession :: Connection -> String -> IO String
startSession conn user =
  do
    -- maybe check for old sessions and clean up?
    let deleteSessionQuery = "DELETE FROM Session WHERE User = ? ;" :: Query
    execute conn deleteSessionQuery [user]
    -- create new session
    timeStamp <- formatTime defaultTimeLocale "%s" <$> getCurrentTime 
    let sessionData = user ++ timeStamp
    let token = show (hash (B.pack sessionData) :: Digest SHA3_512) :: String
    let insertSessionQuery = "INSERT INTO Session (Token,User,Starttime,LastActive) VALUES (?,?,?,?);" :: Query
    execute conn insertSessionQuery (token,user,timeStamp,timeStamp)
    return token

updateActivity :: Connection -> String -> IO()
updateActivity conn token =
  do
    timeStamp <- formatTime defaultTimeLocale "%s" <$> getCurrentTime 
    let updateSessionLastActiveQuery = "UPDATE Session SET LastActive = ? WHERE Token = ?;" :: Query
    execute conn updateSessionLastActiveQuery (timeStamp,token)

verifySession :: Connection -> String -> IO (Bool,String)
verifySession conn token =
  do
    -- Get potential user session(s)
    let selectSessionQuery = "SELECT LastActive FROM Session WHERE Token = ?;" :: Query
    sessions <- query conn selectSessionQuery [token] :: IO [Only Int]
    -- from here might not be executed due to lazy evaluation...
    -- Compute the difference in time stamps
    let oldTimeStamp = fromOnly . head $ sessions
    timeStamp <- formatTime defaultTimeLocale "%s" <$> getCurrentTime 
    let newTimeStamp = read timeStamp :: Int
    let deleteSessionQuery = "DELETE FROM Session WHERE Token = ? ;"
    let error = if length sessions == 0 then "Not current session" else if newTimeStamp - oldTimeStamp > 60 * 30 then "Session timeout" else "More than one session"
    -- ... until here. check if a session exists and it is has been active in the last 30 minutes
    if length sessions == 1 && newTimeStamp - oldTimeStamp <= 60*30 then return (True,"")
      else do { execute conn deleteSessionQuery [token] ; return (False,error) }

-- | List all the lessons i.e. lesson name, description and exercise count
listLessons :: Connection -> String -> IO [(String,String,Int,Int,Int,Int,Bool,Bool)]
listLessons conn token =
  do
    let listUserQuery = "SELECT User FROM Session WHERE Token = ?;" :: Query
    let listLessonsQuery =
          Query $ T.pack $ "WITH userName AS (SELECT ?), " ++
                           "maxRounds AS (SELECT Lesson,IFNULL(MAX(Round),0) AS Round FROM (SELECT * FROM StartedLesson UNION SELECT Lesson,User,Round FROM FinishedLesson) WHERE User = (SELECT * FROM userName) GROUP BY Lesson) " ++
                           "SELECT Name, Description, ExerciseCount," ++
                           "(SELECT COUNT(*) AS Passed FROM FinishedExercise WHERE " ++
                           "User = (SELECT * FROM userName) AND Lesson = Name AND Round = (SELECT Round FROM maxRounds WHERE User = (SELECT * FROM userName) AND Lesson = Name)) AS Passed, " ++
                           "(SELECT IFNULL(SUM(ClickCount),0) FROM FinishedExercise F WHERE " ++
                           "User = (SELECT * from UserName) AND Lesson = Name  AND Round = (SELECT Round FROM maxRounds WHERE User = (SELECT * FROM userName) AND Lesson = Name)) AS Score, " ++
                           "(SELECT IFNULL(SUM(Time),0) FROM FinishedExercise F WHERE " ++
                           "User = (SELECT * from UserName) AND Lesson = Name  AND Round = (SELECT Round FROM maxRounds WHERE User = (SELECT * FROM userName) AND Lesson = Name)) AS Time, " ++
                           "(SELECT MIN(IFNULL(COUNT(*),0),1) FROM FinishedLesson WHERE " ++
                           "User = (SELECT * from UserName) AND Lesson = Name) AS Passed, " ++
                           "Enabled " ++
                           "FROM Lesson;" :: Query -- TODO probably more test data?
    users <- query conn listUserQuery [token] :: IO [Only String]
    if length users == 1 then
      let user = fromOnly . head $ users in query conn listLessonsQuery [user] :: IO [(String,String,Int,Int,Int,Int,Bool,Bool)]
      else
      throw $ DatabaseException "More or less than expected numbers of users"
    
    
-- | start a new lesson by randomly choosing the right number of exercises and adding them to the users exercise list
startLesson :: Connection -> String -> String -> IO (String,String,String,String)
startLesson conn token lesson =
  do
    -- get user name
    let userQuery = "SELECT User FROM Session WHERE Token = ?;" :: Query
    [[user]] <- query conn userQuery [token] :: IO [[String]]
    let checkLessonStartedQuery = "SELECT COUNT(*) FROM StartedLesson WHERE User = ? AND Lesson = ?" :: Query
    isRunning <- (0 /=) . fromOnly . head <$> (query conn checkLessonStartedQuery [user,lesson] :: IO [Only Int])
    if isRunning then
      continueLesson conn user lesson
      else
      newLesson conn user lesson
     
newLesson :: Connection -> String -> String -> IO (String,String,String,String)
newLesson conn user lesson =
  do
    -- get exercise count
    let exerciseCountQuery = "SELECT ExerciseCount FROM Lesson WHERE Name = ?;" :: Query
    [[count]] <- query conn exerciseCountQuery [lesson] :: IO [[Int]]
    -- get lesson round
    let lessonRoundQuery = "SELECT ifnull(MAX(Round),0) FROM FinishedExercise WHERE User = ? AND Lesson = ?;" :: Query
    [[round]] <- query conn lessonRoundQuery [user,lesson] :: IO [[Int]]
    -- get all exercises for lesson
    let exerciseQuery = "SELECT SourceTree,TargetTree FROM Exercise WHERE Lesson = ?;" :: Query
    trees <- query conn exerciseQuery [lesson] :: IO [(String,String)]
    -- randomly select
    selectedTrees <- fmap (take count) $ generate $ shuffle trees
    -- save in database
    let insertStartedLesson = "INSERT INTO StartedLesson (Lesson, User, Round) VALUES (?,?,?);" :: Query
    execute conn insertStartedLesson (lesson,user,round + 1)
    let insertExerciseList = "INSERT INTO ExerciseList (Lesson,User,SourceTree,TargetTree,Round) VALUES (?,?,?,?,?);" :: Query
    let ((sourceTree,targetTree):_) = selectedTrees
    mapM_ (\(sTree,tTree) -> execute conn insertExerciseList (lesson,user,sTree,tTree,round)) selectedTrees
    -- get languages
    let languagesQuery = "SELECT SourceLanguage, TargetLanguage FROM Lesson WHERE Name = ?;" :: Query
    langs <- query conn languagesQuery [lesson] :: IO [(String,String)]
    if length langs == 1 then 
      let (sourceLang,targetLang) = head langs in return (sourceLang,sourceTree,targetLang,targetTree)
      else
      throw $ DatabaseException "Couldn't find the languages"

continueLesson :: Connection -> String -> String -> IO (String,String,String,String)
continueLesson conn user lesson =
  do
    -- get lesson round
    let lessonRoundQuery = "SELECT ifnull(MAX(Round),0) FROM FinishedExercise WHERE User = ? AND Lesson = ?;" :: Query
    [[round]] <- query conn lessonRoundQuery [user,lesson] :: IO [[Int]]
    let selectExerciseListQuery = "SELECT SourceTree,TargetTree FROM ExerciseList WHERE Lesson = ? AND User = ? AND (User,SourceTree,TargetTree,Lesson) NOT IN (SELECT User,SourceTree,TargetTree,Lesson FROM FinishedExercise WHERE Round = ?);" :: Query
    ((sourceTree,targetTree):_) <- query conn selectExerciseListQuery (lesson,user,round) :: IO [(String,String)]
    let languagesQuery = "SELECT SourceLanguage, TargetLanguage FROM Lesson WHERE Name = ?;" :: Query
    [(sourceLang,targetLang)] <- query conn languagesQuery [lesson] :: IO [(String,String)]
    return (sourceLang,sourceTree,targetLang,targetTree)

finishExercise :: Connection -> String -> String -> Int -> Int -> IO ()
finishExercise conn token lesson time clicks =
  do
    -- get user name
    let userQuery = "SELECT User FROM Session WHERE Token = ?;" :: Query
    [[user]] <- query conn userQuery [token] :: IO [[String]]
    -- get lesson round
    let lessonRoundQuery = "SELECT ifnull(MAX(Round),1) FROM StartedLesson WHERE User = ? AND Lesson = ?;" :: Query
    [[round]] <- query conn lessonRoundQuery [user,lesson] :: IO [[Int]]
    let selectExerciseListQuery = "SELECT SourceTree,TargetTree FROM ExerciseList WHERE Lesson = ? AND User = ? AND (User,SourceTree,TargetTree,Lesson) NOT IN (SELECT User,SourceTree,TargetTree,Lesson FROM FinishedExercise WHERE Round = ?);" :: Query
    ((sourceTree,targetTree):_) <- query conn selectExerciseListQuery (lesson,user,round) :: IO [(String,String)]
    let insertFinishedExerciseQuery = "INSERT INTO FinishedExercise (User,Lesson,SourceTree,TargetTree,Time,ClickCount,Round) VALUES (?,?,?,?,?,?,?);" :: Query
    execute conn insertFinishedExerciseQuery (user, lesson, sourceTree, targetTree, time, clicks + 1, round)
    -- check if all exercises finished
    let countFinishesExercisesQuery = "SELECT COUNT(*) FROM FinishedExercise F WHERE User = ? AND Lesson = ? AND Round = (SELECT MAX(Round) FROM StartedLesson WHERE User = F.User AND Lesson = F.Lesson);" :: Query
    let countExercisesInLesson = "SELECT ExerciseCount FROM Lesson WHERE Name = ?;" :: Query
    let deleteStartedLessonQuery = "DELETE FROM StartedLesson WHERE User = ? AND Lesson = ? ;" :: Query
    let insertFinishedLessonQuery =
          Query $ T.pack $ "WITH userName AS (SELECT ?)," ++
                           "lessonName AS (SELECT ?)," ++
                           "roundCount as (SELECT MAX(Round) FROM StartedLesson WHERE User = (SELECT * FROM userName) AND Lesson = (SELECT * FROM lessonName)) " ++
                           "INSERT INTO FinishedLesson (User,Lesson,Time,ClickCount,Round) VALUES " ++
                           "((SELECT * FROM userName)," ++
                           "(SELECT * FROM lessonName)," ++
                           "(SELECT SUM(Time) FROM FinishedExercise WHERE User = (SELECT * FROM userName) AND Lesson = (SELECT * FROM lessonName) AND Round = (SELECT * FROM roundCount))," ++
                           "(SELECT SUM(clickcount) FROM FinishedExercise WHERE User = (SELECT * FROM userName) AND Lesson = (SELECT * FROM lessonName) AND Round = (SELECT * FROM roundCount))," ++
                           "(SELECT * FROM roundCount));"
    [[finishedCount]] <- query conn countFinishesExercisesQuery [user,lesson] :: IO [[Int]]
    [[exerciseCount]] <- query conn countExercisesInLesson [lesson] :: IO [[Int]]
    if finishedCount >= exerciseCount then do
      execute conn insertFinishedLessonQuery [user,lesson]
      execute conn deleteStartedLessonQuery [user,lesson]
      else return ()

endSession :: Connection -> String -> IO ()
endSession conn token =
  do
    let deleteSessionQuery = "DELETE FROM Session WHERE Token = ?;" :: Query
    execute conn deleteSessionQuery [token]
    
