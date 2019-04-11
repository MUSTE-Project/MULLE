-- | Handles CRUD operations (and a bit of logic).
--
-- Module      : Muste.Web.Database
-- License     : Artistic License 2.0
-- Stability   : experimental
-- Portability : POSIX

{-# OPTIONS_GHC -Wall #-}
{-# Language
 DeriveAnyClass,
 NamedFieldPuns,
 OverloadedStrings,
 RecordWildCards,
 ScopedTypeVariables,
 TypeApplications
#-}

module Muste.Web.Database
  ( MonadDB
  , DbT(DbT)
  , Db
  , HasConnection(..)
  , getConnection
  , Error(..)
  , MonadDatabaseError(..)
  , runDbT
  , getLessons
  , authUser
  , startSession
  , getActiveLessons
  , startLesson
  , finishExercise
  , endSession
  , verifySession
  , addUser
  , changePassword
  , updateActivity
  , rmUser
  , getUserLessonScores
  , resetLesson
  ) where

import Control.Exception (fromException)
import Control.Monad (void, when)
import Control.Monad.IO.Class (MonadIO(liftIO))

import Database.SQLite.Simple (Only(..), NamedParam(..))
import qualified Database.SQLite.Simple as SQL

import qualified Crypto.Random as Crypto
import qualified Crypto.KDF.PBKDF2 as Crypto
import qualified Crypto.Hash as Crypto

import Data.List (sortOn)
import Data.ByteString (ByteString)
import Data.String.Conversions (convertString)
import Data.Text (Text)
import qualified Data.Text.Encoding as T
import Data.Time (NominalDiffTime)
import Data.Time.Clock (UTCTime)
import qualified Data.Time.Clock as Time
import qualified Data.Time.Format as Time

-- FIXME QuickCheck seems like a heavy dependency just to get access to `shuffle`.
import qualified Test.QuickCheck as QC (shuffle, generate)

import qualified Muste.Web.Database.Types as Types
import qualified Muste.Web.Database.Types as ExerciseLesson (ExerciseLesson(..))
import qualified Muste.Web.Database.Types as User (User(..))
import Muste.Web.Types.Score (Score)

import Muste.Web.Database.Class
  ( MonadDB
  , Error(..)
  , executeNamed
  , queryNamed
  , DbT(..)
  , Db
  , HasConnection(..)
  , getConnection
  , MonadDatabaseError(..)
  , runDbT
  , query_
  , executeManyNamed
  )


-- | @'hashPasswd' pw salt@ encodes @pw@ using PBKDF2 (using @salt@ as
-- cyrptographic salt, doing 1e4 iterations and creating 1KiB
-- output). It then SHA 512 encodes this.
hashPassword
  :: Text       -- ^ Password in clear text
  -> ByteString -- ^ Salt
  -> Types.Blob
hashPassword pw salt
  = Types.Blob
  $ Crypto.fastPBKDF2_SHA512 p t salt
  where
  p = Crypto.Parameters 10000 1024
  t = T.encodeUtf8 pw

-- | 'createSalt' returns a SHA512 hash of 512 bytes of random data as
-- a 'ByteString'.
createSalt :: MonadIO io => io ByteString
createSalt
  =   fst
  .   Crypto.randomBytesGenerate 512
  <$> liftIO Crypto.getSystemDRG

getCurrentTime :: MonadIO io => io UTCTime
getCurrentTime = liftIO Time.getCurrentTime

getLessons :: MonadDB r db => db [Types.Lesson]
getLessons = query_ lessonBaseQuery

getLesson :: MonadDB r db => Types.Key Types.Lesson -> db Types.Lesson
getLesson l = head <$> queryNamed q [":Lesson" := l]
  where q = lessonBaseQuery <> " WHERE Id = :Lesson "

lessonBaseQuery :: SQL.Query
lessonBaseQuery = 
  " SELECT Id, Name, Grammar, SourceLanguage, TargetLanguage, ExerciseCount,        \
  \        Enabled, SearchLimitDepth, SearchLimitSize, Repeatable, SourceDirection, \
  \        TargetDirection, HighlightMatches, ShowSourceSentence, RandomizeOrder    \
  \ FROM Lesson "

-- FIXME In this contexts the naming suggests that the user is
-- persisted.  Consider changin.
-- | Generates an instance of 'Types.User' suitable for inserting into
-- the database.  Note that this function does /not/ persist the user.
createUser
  :: MonadDB r db
  => Types.CreateUser
  -> db Types.User
createUser Types.CreateUser{..} = do
  -- Create a salted password
  salt <- createSalt
  pure $ Types.User
    { name     = name
    , password = hashPassword password salt
    , salt     = Types.Blob salt
    , enabled  = enabled
    }

-- | Adds a new user to the database.
addUser
  :: MonadDB r db
  => Types.CreateUser
  -> db ()
addUser usr = do
  Types.User{..} <- createUser usr
  let u = [ ":Username"  := name
          , ":Password"  := password
          , ":Salt"      := salt
          , ":Enabled"   := enabled
          ]
  executeNamed q u `catchDbError` h
  where
  h e = case e of
    DriverError de -> case fromException de of
      Just (SQL.SQLError SQL.ErrorConstraint{} _ _)
        -- This error is likely due to the fact that the user already
        -- exists.
        -> throwDbError UserAlreadyExists
      _ -> throwDbError e
    _ -> throwDbError e
  q = " INSERT INTO User (Username, Password, Salt, Enabled) \
      \ VALUES (:Username, :Password, :Salt, :Enabled) "

-- | Removes an existing user from the database.
rmUser
  :: MonadDB r db
  => Text
  -> db ()
rmUser u = void $ executeNamed q [ ":User" := u ]
  where
    q = " DELETE FROM User WHERE Username = :User "

authUser
  :: MonadDB r db
  => Text -- ^ Username
  -> Text -- ^ Password
  -> db ()
authUser user pass = do
  -- Get password and salt from database
  userList <- queryNamed q [":Username" := user]
  -- Generate new password hash and compare to the stored one
  let
    h (Types.Blob s) = hashPassword pass s
    p Types.User{..} = enabled && h salt == password
  case userList of
    [usr] -> if p usr then return ()
             else throwDbError NotAuthenticated
    _     -> throwDbError NoUserFound
  where
    q = " SELECT Username, Password, Salt, Enabled \
        \ FROM User WHERE Username = :Username "

changePassword
  :: MonadDB r db
  => Types.ChangePassword
  -> db ()
changePassword Types.ChangePassword{..} = do
  authUser name oldPassword
  rmUser name
  addUser $ Types.CreateUser
    { name     = name
    , password = newPassword
    , enabled  = True
    }

createSession
  :: MonadDB r db
  => Text
  -> db Types.Session
createSession user = do
  -- Remove any existing session.
  executeNamed q [":User" := user]
  -- Create new session.
  timeStamp <- getCurrentTime
  pure $ Types.Session
    { user       = user
    , token      = genToken timeStamp
    , startTime  = timeStamp
    , lastActive = timeStamp
    }
  where
    q = " DELETE FROM Session WHERE User = :User "

endSession
  :: MonadDB r db
  => Types.Token
  -> db ()
endSession t = executeNamed q [ ":Token" := t ]
  where
    q = " DELETE FROM Session WHERE Token = :Token "

-- FIXME Reduce the three-layered string conversion going on here.
genToken :: UTCTime -> Types.Token
genToken timeStamp
  = Types.Token
  $ convertString
  $ show
  $ Crypto.hash @ByteString @Crypto.SHA3_512
  $ convertString
  $ formatTime timeStamp

-- | Creates a new session and returns the session token.  At the
-- moment overly simplified.
startSession
  :: MonadDB r db
  => Text
  -> db Types.Token
startSession usr = do
  Types.Session user token startTime lastActive <- createSession usr
  let n = [ ":User"        := user
          , ":Token"       := token
          , ":Starttime"   := startTime
          , ":LastActive"  := lastActive
          ]
  executeNamed q n
  return token
  where q = " INSERT INTO Session (User, Token, Starttime, LastActive) \
            \ VALUES (:User, :Token, :Starttime, :LastActive) "

formatTime :: UTCTime -> String
formatTime = Time.formatTime Time.defaultTimeLocale "%s"

updateActivity
  :: MonadDB r db
  => Types.Token
  -> db ()
updateActivity token = do
  -- We should use to- from- row instances for UTCTime in stead.
  timeStamp <- formatTime <$> getCurrentTime
  executeNamed q [ ":LastActive" := timeStamp, ":Token" := token ]
  where
    q = " UPDATE Session SET LastActive = :LastActive \
        \ WHERE Token = :Token "

-- | Throws @SessionTimeout@ if the session has timed out.
verifySession
  :: MonadDB r db
  => Types.Token
  -> db ()
verifySession token = do
  -- Get potential user session(s)
  sessions <- getLastActive token
  -- from here might not be executed due to lazy evaluation...
  -- Compute the difference in time stamps
  newTimeStamp <- getCurrentTime
  -- ... until here. check if a session exists and it is has been
  -- active in the last 30 minutes
  case expired sessions newTimeStamp of
    Nothing -> pure ()
    Just err -> do
      deleteSession token
      throwDbError err

-- Check if the token has expired.
expired :: UTCTime -> UTCTime -> Maybe Error
expired oldTimeStamp newTimeStamp
  | diff <= sessionLifeTime = Nothing
  | otherwise               = Just SessionTimeout
  where
  diff = newTimeStamp `Time.diffUTCTime` oldTimeStamp

-- TODO Make this configurable.
sessionLifeTime :: NominalDiffTime
sessionLifeTime = 30 * h
  where
  m = 60
  h = 60 * m

getLastActive
  :: MonadDB r db
  => Types.Token
  -> db UTCTime
getLastActive t = do
  xs <- queryNamed q [":Token" := t]
  case xs of
    []         -> throwDbError NotCurrentSession
    (Only x:_) -> pure x
  where
    q = " SELECT LastActive FROM Session WHERE Token = :Token "

deleteSession
  :: MonadDB r db
  => Types.Token
  -> db ()
deleteSession token = executeNamed q [ ":Token" := token ]
  where
    q = " DELETE FROM Session WHERE Token = :Token "

-- | List all the lessons i.e. lesson name and exercise
-- count
getActiveLessons
  :: forall r db . MonadDB r db
  => Types.Token
  -> db [Types.ActiveLessonForUser]
getActiveLessons token = do
  user <- getUser token
  getActiveLessonsForUser user

getActiveLessonsForUser
  :: forall r db . MonadDB r db
  => Text
  -> db [Types.ActiveLessonForUser]
getActiveLessonsForUser user = queryNamed q [":User" := user]
  where
    q = " SELECT Lesson.Id AS Lesson, Lesson.Name, \
        \ COALESCE(ExerciseCount,0) AS ExerciseCount, \
        \ Score, Lesson.Enabled, FinishedExercise.User \
        \ FROM Exercise \
        \ JOIN Lesson ON Exercise.Lesson = Lesson.Id \
        \ LEFT \
        \ JOIN FinishedExercise \
        \ ON   FinishedExercise.Exercise = Exercise.Id \
        \ AND  User = :User  OR  User IS NULL "

-- | Start a new lesson by randomly choosing the right number of
-- exercises and adding them to the users exercise list
startLesson
  :: MonadDB r db
  => Types.Token
  -> Types.Key Types.Lesson
  -> db Types.ExerciseLesson
startLesson token lesson = do
  user <- getUser token
  isRunning <- checkStarted user lesson
  if isRunning
  then continueLesson user lesson
  else newLesson      user lesson

checkStarted
  :: MonadDB r db
  => Text
  -> Types.Key Types.Lesson
  -> db Bool
checkStarted user lesson
  =   ((0 :: Int) /=) . fromOnly . head
  <$> queryNamed q [":User" := user, ":Lesson" := lesson]
  where
    q = " SELECT COUNT(*) FROM UnfinishedLesson \
        \ WHERE  User = :User  AND  Lesson = :Lesson "

getUser
  :: MonadDB r db
  => Types.Token
  -> db Text
getUser token = do
  xs <- queryNamed q [":Token" := token]
  case xs of
    []       -> throwDbError NoUserFound
    [Only x] -> pure x
    _        -> throwDbError MultipleUsers
  where
    q = " SELECT User FROM Session WHERE Token = :Token "

shuffle :: MonadIO m => [a] -> m [a]
shuffle = liftIO . QC.generate . QC.shuffle

getExerciseLessons
  :: MonadDB r db
  => Types.Key Types.Lesson
  -> db [Types.ExerciseLesson]
getExerciseLessons lesson = queryNamed q [":Lesson" := lesson]
  where
  q = " SELECT Exercise, Lesson, Name, SourceTree, TargetTree, \
      \        SourceDirection, TargetDirection, HighlightMatches, \
      \        ShowSourceSentence, ExerciseOrder \
      \ FROM   ExerciseLesson \
      \ WHERE  Lesson = :Lesson "

newLesson
  :: MonadDB r db
  => Text
  -> Types.Key Types.Lesson
  -> db Types.ExerciseLesson
newLesson user lesson = do
  lessonRound <- getLessonRound user lesson
  -- FIXME To reduce confusing we will disallow re-starting exercises
  -- until we know what we really want to do in this situation.
  finished <- checkFinished user lesson
  when finished $ throwDbError LessonAlreadySolved
  selectedTrees <- pickExercises lesson
  exerciseLesson <- case selectedTrees of
    []      -> throwDbError NoExercisesInLesson
    (x : _) -> pure x
  -- save in database
  startLessonAux $ Types.StartedLesson lesson user lessonRound
  let
    step :: (Types.Numeric, Types.ExerciseLesson) -> Types.ExerciseList
    step (round', Types.ExerciseLesson{..}) -- (exercise, _name, _, _)
      = Types.ExerciseList
      { user     = user
      , exercise = exercise
      , round    = round'
      , score    = Nothing
      }
  insertExercises $ step <$> zip [lessonRound..] selectedTrees
  pure exerciseLesson

-- | Picks a new set of exercises for a lesson.  The number we pick is
-- given by the lesson.  The lesson also says if we should present the
-- exercises in a randomized order or use the @ExerciseOrder@ column
-- of the @Exercise@ table to decide this.
pickExercises
  :: MonadDB r db
  => Types.Key Types.Lesson
  -> db [Types.ExerciseLesson]
pickExercises lesson = do
  Types.Lesson{..} <- getLesson lesson
  es <- take (fromIntegral exerciseCount) <$> getExerciseLessons lesson
  if randomizeOrder
  then shuffle es
  else pure $ sortOn ExerciseLesson.exerciseOrder es

startLessonAux :: MonadDB r db => Types.StartedLesson -> db ()
startLessonAux (Types.StartedLesson lesson user round') =
  executeNamed
  " INSERT INTO StartedLesson (Lesson, User, Round) \
  \ VALUES (:Lesson, :User, :Round) "
  [ ":Lesson"   := lesson
  , ":User"     := user
  , ":Round"    := round'
  ]

insertExercises :: MonadDB r db => [Types.ExerciseList] -> db ()
insertExercises exercises =
  executeManyNamed q
  [ [ ":User"     := user
    , ":Exercise" := exercise
    , ":Round"    := round'
    , ":Score"    := score
    ]
  | Types.ExerciseList user exercise round' score <- exercises ]

  where q = " INSERT INTO ExerciseList (User, Exercise, Round, Score) \
            \ VALUES (:User, :Exercise, :Round, :Score) "

-- FIXME It makes more sense to query @StartedLesson@ to figure out
-- how far along the lesson is or perhaps implement this as a view or
-- something.  Should be more robust...
getLessonRound
  :: MonadDB r db
  => Text
  -> Types.Key Types.Lesson
  -> db Types.Numeric
getLessonRound user lesson =
  fromOnly . head <$> queryNamed q [ ":User" := user, ":Lesson" := lesson ]
  where
    q = " SELECT ifnull(MAX(ExerciseList.Round) + 1,0) \
        \ FROM   ExerciseList \
        \ JOIN   Exercise ON ExerciseList.Exercise = Exercise.Id \
        \ WHERE  ExerciseList.User = :User \
        \   AND  Lesson = :Lesson \
        \   AND  Score IS NOT NULL "

continueLesson
  :: MonadDB r db
  => Text
  -> Types.Key Types.Lesson
  -> db Types.ExerciseLesson
continueLesson user lesson = do
  round' <- getLessonRound user lesson
  getExercise lesson user round'

-- FIXME Add 'FinishExercise' type.
finishExercise
  :: MonadDB r db
  => Types.Token
  -> Types.Key Types.Lesson
  -> Score
  -> db Bool
finishExercise token lesson score = do
  -- get user name
  user <- getUser token
  -- get lesson round
  round' <- getLessonRound user lesson
  Types.ExerciseLesson{..} <- getExercise lesson user round'
  finishExerciseAux $ Types.ExerciseList
    { user     = user
    , exercise = exercise
    , round    = round'
    , score    = Just score
    }
  finished <- checkFinished user lesson
  when finished $ finishLesson user lesson round'
  pure finished

checkFinished
  :: MonadDB r db
  => Text
  -> Types.Key Types.Lesson
  -> db Bool
checkFinished user lesson = do
  finishedCount <- getFinishedExercises user lesson
  exerciseCount <- getExerciseCount lesson
  pure $ finishedCount >= exerciseCount

-- | This method will update the score for a given @StartedLesson@ and
-- ensure that there is only one entry per user/lesson combination.
finishLesson
  :: MonadDB r db
  => Text
  -> Types.Key Types.Lesson
  -> Types.Numeric -- ^ Round
  -> db ()
finishLesson user lesson round' = do
  score <- getScore user lesson
  deleteStartedLessons user lesson
  executeNamed
    " INSERT INTO StartedLesson (Lesson, User, Round, Score) \
    \ VALUES  (:Lesson, :User, :Round, :Score) "
    [ ":Lesson" := lesson
    , ":User"   := user
    , ":Score"  := score
    , ":Round"  := succ round'
    ]

deleteStartedLessons
  :: MonadDB r db
  => Text
  -> Types.Key Types.Lesson
  -> db ()
deleteStartedLessons u l = executeNamed q [":User" := u, ":Lesson" := l]
  where
    q = " DELETE FROM StartedLesson \ 
        \ WHERE  User = :User  AND  Lesson = :Lesson "

-- | Gets an unfinished exercise.
getExercise
  :: MonadDB r db
  => Types.Key Types.Lesson
  -> Text
  -> Types.Numeric -- ^ Round
  -> db Types.ExerciseLesson
getExercise lesson user round' =
  do xs <- queryNamed q [ ":Lesson" := lesson, ":User" := user, ":Round" := round' ]
     case xs of
       [x] -> pure x
       _   -> throwDbError NoActiveExercisesInLesson
  where
    q = " SELECT Exercise, Lesson.Id, Lesson.Name, SourceTree, TargetTree, \
        \        SourceDirection, TargetDirection, HighlightMatches, \
        \        ShowSourceSentence, ExerciseOrder \
        \ FROM   ExerciseList \
        \ JOIN   Exercise ON Exercise = Exercise.Id \
        \ JOIN   Lesson   ON Lesson   = Lesson.Id \
        \ WHERE  Lesson = :Lesson \
        \   AND  User   = :User \
        \   AND  Round  = :Round \
        \   AND  Score IS NULL "

finishExerciseAux
  :: MonadDB r db
  => Types.ExerciseList
  -> db ()
finishExerciseAux (Types.ExerciseList user exercise round' score) =
  executeNamed
  " UPDATE ExerciseList SET Score = :Score \
  \ WHERE  User = :User  AND  Exercise = :Exercise  AND  Round = :Round "
  [ ":User"      := user
  , ":Exercise"  := exercise
  , ":Round"     := round'
  , ":Score"     := score
  ]

getFinishedExercises
  :: MonadDB r db
  => Text
  -> Types.Key Types.Lesson
  -> db Types.Numeric
getFinishedExercises user lesson
  =   fromOnly . head
  <$> queryNamed q [ ":User" := user, ":Lesson" := lesson ]
  where
    q = " SELECT COUNT(*) FROM ExerciseList \
        \ JOIN   Exercise ON Exercise = Exercise.Id \
        \ JOIN   Lesson   ON Lesson   = Lesson.Id \
        \ WHERE  User = :User  AND  Lesson = :Lesson  AND  Score NOT NULL "

getExerciseCount
  :: MonadDB r db
  => Types.Key Types.Lesson
  -> db Types.Numeric
getExerciseCount lesson =
  fromOnly . head <$> queryNamed q [":Lesson" := lesson]
  where
    q = " SELECT ExerciseCount FROM Lesson WHERE Id = :Lesson "

-- | Get the score for the user and lesson.
getScore
  :: MonadDB r db
  => Text
  -> Types.Key Types.Lesson
  -> db Score
getScore user lesson
  =   mconcat . fmap fromOnly
  <$> queryNamed q
  [ ":User"   := user
  , ":Lesson" := lesson
  ]
  where
    q = " SELECT Score FROM ExerciseList \
        \ JOIN   Exercise ON Exercise = Exercise.Id \
        \ WHERE  User = :User  AND  Lesson = :Lesson  AND  Score NOT NULL "

-- | The user and their score on each excercise.  If score and user is
-- null this means that /no/ user has completed the exercise.  If a
-- given exercise/user combination is not present in the output, then
-- this means that /this/ user has not completed the exercise.
getUserLessonScores
  :: MonadDB r db
  => db [Types.UserLessonScore]
getUserLessonScores =
  query_ 
  " SELECT Lesson.Id, Lesson.Name, User.Username, FinishedLesson.Score \
  \ FROM   FinishedLesson \
  \ JOIN   User \
  \   ON   User = User.Username \
  \ LEFT \
  \   JOIN Lesson \
  \   ON   Lesson = Lesson.Id "

resetLesson
  :: MonadDB r db
  => Types.Token
  -> Types.Key Types.Lesson
  -> db ()
resetLesson t l = do
  u <- getUser t
  deleteExerciseList u l

-- | Deletes the exercise for a given user/lesson.
deleteExerciseList
  :: MonadDB r db
  => Text
  -> Types.Key Types.Lesson
  -> db ()
deleteExerciseList u l = executeNamed q [":User" := u, ":Lesson" := l]
  where
    q = " DELETE FROM ExerciseList \ 
        \ WHERE  User = :User \
        \   AND  Exercise IN ( SELECT Id FROM Exercise WHERE Lesson = :Lesson ) "
