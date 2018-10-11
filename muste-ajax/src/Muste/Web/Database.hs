-- FIXME So many methods need access to a lesson and a user.  Perhaps
-- we should just add this to the database monad.
-- TODO Fix name shadowing.
{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
{-# Language QuasiQuotes, RecordWildCards, MultiWayIf, DeriveAnyClass, NamedFieldPuns #-}
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
  ) where

import Prelude ()
import Muste.Prelude
import qualified Muste.Prelude.Unsafe as Unsafe
import Muste.Prelude.Extra
import Muste.Prelude.SQL
  ( Query, Connection, Only(Only), fromOnly
  , ToRow, FromRow, sql
  )
import qualified Muste.Prelude.SQL as SQL

import qualified Data.List.NonEmpty as NonEmpty

import Crypto.Random.API (getSystemRandomGen, genRandomBytes)
import Crypto.KDF.PBKDF2 (fastPBKDF2_SHA512, Parameters(Parameters))
import Crypto.Hash (SHA3_512, hash)

import Data.ByteString (ByteString)
import qualified Data.Text.Encoding     as T
import qualified Data.Time.Clock        as Time
import qualified Data.Time.Format       as Time
import Control.Monad.Reader

-- FIXME QuickCheck seems like a heavy dependency just to get access
-- to `shuffle`.
import qualified Test.QuickCheck as QC (shuffle, generate)

import qualified Muste

import qualified Muste.Web.Database.Types as Types
import qualified Muste.Web.Database.Types as ActiveLessonForUser (ActiveLessonForUser(..))
import           Muste.Web.Types.Score (Score)

data Error
  = NoUserFound
  | LangNotFound
  | MultipleUsers
  | NoCurrentSession
  | SessionTimeout
  | MultipleSessions
  | NoExercisesInLesson
  | NonUniqueLesson
  | NotAuthenticated
  | DriverError SomeException
  | UserAlreadyExists

deriving stock instance Show Error
instance Exception Error where
  displayException = \case
    NoUserFound         → "No user found."
    LangNotFound        → "Could not find the languages."
    MultipleUsers
      →  "Well this is embarrasing.  "
      <> "It would appear that someone managed "
      <> "to steal youre identity."
    NoCurrentSession    → "Not current session"
    SessionTimeout      → "Session timeout"
    MultipleSessions    → "More than one session"
    NoExercisesInLesson → "No exercises for lesson"
    NonUniqueLesson     → "Non unique lesson"
    NotAuthenticated    → "User is not authenticated"
    DriverError e
      →  "Unhandled driver error: "
      <> displayException e
    UserAlreadyExists → "The username is taken"

-- | hashPasswd returns a SHA512 hash of a PBKDF2 encoded password
-- (SHA512,10000 iterations,1024 bytes output)
hashPasswd :: ByteString -> ByteString -> ByteString
hashPasswd = fastPBKDF2_SHA512 $ Parameters 10000 1024

-- | createSalt returns a SHA512 hash of 512 bytes of random data as a
-- bytestring
createSalt :: MonadIO io ⇒ io ByteString
createSalt = fst . genRandomBytes 512 <$> liftIO getSystemRandomGen

getCurrentTime ∷ MonadIO io ⇒ io UTCTime
getCurrentTime = liftIO Time.getCurrentTime

getLessons
  :: MonadDB r db
  => db [Types.Lesson]
getLessons = query_ 
  [sql|
-- getLessons
SELECT
    Id
  , Name
  , Description
  , Grammar
  , SourceLanguage
  , TargetLanguage
  , ExerciseCount
  , Enabled
  , SearchLimitDepth
  , SearchLimitSize
  , Repeatable
FROM Lesson;
|]

-- FIXME In this contexts the naming suggests that the user is
-- persisted.  Consider changin.
-- | Generates an instance of 'Types.User' suitable for inserting into
-- the database.  Note that this function does /not/ persist the user.
createUser
  :: MonadDB r db
  => Text -- ^ Username
  -> Text -- ^ Password
  -> Bool -- ^ User enabled
  -> db Types.User
createUser user pass enabled = do
  -- Create a salted password
  salt <- createSalt
  let safePw = hashPasswd (T.encodeUtf8 pass) salt
  pure $ Types.User user safePw salt enabled

-- | Adds a new user to the database.
addUser
  ∷ MonadDB r db
  ⇒ Text -- ^ Username
  → Text -- ^ Password
  → Bool -- ^ User enabled
  → db ()
addUser user pass enabled = do
  u ← createUser user pass enabled
  execute q u `catchDbError` h
  where
  h e = case e of
    -- DriverError e → case fromException @SQL.ResultError $ toException e of
    DriverError de → case fromException @SQL.SQLError de of
      Just (SQL.SQLError SQL.ErrorConstraint{} _ _)
        -- This error is likely due to the fact that the user already
        -- exists.
        → throwDbError UserAlreadyExists
      _ → throwDbError e
    _ → throwDbError e
  q = [sql|
-- addUser
INSERT INTO User (Username, Password, Salt, Enabled) VALUES (?,?,?,?);
|]

-- | Removes an existing user from the database.
rmUser
  ∷ MonadDB r db
  ⇒ Text
  → db ()
rmUser = void . execute q . Only
  where

  q = [sql|
-- rmUser
DELETE
FROM User
WHERE Username = ?;
|]

authUser
  :: MonadDB r db
  => Text -- ^ Username
  -> Text -- ^ Password
  -> db ()
authUser user pass = do
  -- Get password and salt from database
  userList <- query @(ByteString, ByteString, Bool) q [user]
  -- Generate new password hash and compare to the stored one
  let
    h dbSalt = hashPasswd (T.encodeUtf8 pass) dbSalt
    p (dbPass, dbSalt, enabled) = enabled && h dbSalt == dbPass
  case userList of
    [usr] → if
      | p usr     → pure ()
      | otherwise → throwDbError NotAuthenticated
    _             → throwDbError NoUserFound
  where

  q = [sql|
-- authUser
SELECT
  Password,
  Salt,
  Enabled
FROM User
WHERE Username = ?;
|]

changePassword
  ∷ MonadDB r db
  ⇒ Text -- ^ Username
  → Text -- ^ Old password
  → Text -- ^ New password
  → db ()
changePassword user oldPass newPass = do
  authUser user oldPass
  rmUser user
  addUser user newPass True

createSession
  ∷ MonadDB r db
  ⇒ Text -- ^ Username
  → db Types.Session
createSession user = do
    -- maybe check for old sessions and clean up?
    endSession user
    -- create new session
    timeStamp ← getCurrentTime
    pure $ Types.Session
      { user       = user
      , token      = genToken timeStamp
      , startTime  = timeStamp
      , lastActive = timeStamp
      }

endSession ∷ MonadDB r db ⇒ Text → db ()
endSession user = execute q (Only user)
  where
  q = [sql|
-- createSession
DELETE
FROM Session
WHERE User = ?;
|]

-- FIXME Should a token be 'Text' or 'ByteString'?
genToken ∷ UTCTime → Text
genToken timeStamp = convertString (show (hash @ByteString @SHA3_512 sessionData))
  where
  sessionData ∷ ByteString
  sessionData = convertString $ formatTime timeStamp

-- | Creates a new session and returns the session token.  At the
-- moment overly simplified.
startSession
  :: MonadDB r db
  => Text -- ^ Username
  -> db Text
startSession user = do
  session@(Types.Session _ token _ _) <- createSession user
  execute q session
  return token
  where
  q = [sql|
-- startSession
INSERT INTO Session (User, Token, Starttime, LastActive)
VALUES (?,?,?,?);
|]

formatTime ∷ UTCTime → String
formatTime = Time.formatTime Time.defaultTimeLocale "%s"

updateActivity :: MonadDB r db ⇒ Text -> db ()
updateActivity token = do
  -- We should use to- from- row instances for UTCTime in stead.
  timeStamp ← formatTime <$> getCurrentTime
  execute q (timeStamp,token)
  where
  q = [sql|
-- updateActivity
UPDATE Session SET LastActive = ? WHERE Token = ?;
|]

-- | Returns @Just err@ if there is an error.
verifySession
  :: MonadDB r db
  => Text -- ^ Token
  -> db ()
verifySession token = do
  -- Get potential user session(s)
  sessions ← getLastActive token
  -- from here might not be executed due to lazy evaluation...
  -- Compute the difference in time stamps
  newTimeStamp ← getCurrentTime
  -- ... until here. check if a session exists and it is has been active in the last 30 minutes
  case expired sessions newTimeStamp of
    Nothing → pure ()
    Just err → do
      deleteSession token
      throwDbError err

-- Check if the token has expired.
expired ∷ UTCTime → UTCTime → Maybe Error
expired oldTimeStamp newTimeStamp
  | diff <= sessionLifeTime = Nothing
  | otherwise               = Just SessionTimeout
  where
  diff = newTimeStamp `Time.diffUTCTime` oldTimeStamp

-- TODO Make this configurable.
sessionLifeTime ∷ NominalDiffTime
sessionLifeTime = 30 * h
  where
  m = 60
  h = 60 * m

getLastActive ∷ MonadDB r db ⇒ Text → db UTCTime
getLastActive t = fromOnly . Unsafe.head <$> query q (Only t)
  where

  q = [sql|
-- getSession
SELECT LastActive
FROM Session
WHERE Token = ?;
|]

deleteSession ∷ MonadDB r db ⇒ Text → db ()
deleteSession token = execute q (Only token)
  where
  q = [sql|
-- deleteSession
DELETE
FROM Session
WHERE Token = ?;
|]

-- | List all the lessons i.e. lesson name, description and exercise
-- count
getActiveLessons
  ∷ ∀ r db
  . MonadDB r db
  ⇒ Text -- Token
  → db [Types.ActiveLesson]
getActiveLessons token = do
  user <- getUser token
  fmap step . groupOn ActiveLessonForUser.name <$> getActiveLessonsForUser user
  where
  step ∷ (NonEmpty Types.ActiveLessonForUser) → Types.ActiveLesson
  step xs@(Types.ActiveLessonForUser{..} :| _) = Types.ActiveLesson
    { lesson        = lesson
    , name          = name
    , description   = description
    , exercisecount = exercisecount
    , score         = foldMap (SQL.runNullable . ActiveLessonForUser.score) xs
    , finished      = passedcount == exercisecount
    , enabled       = enabled
    -- , passedcount   = NonEmpty.length xs
    , passedcount   = passedcount
    }
    where
    passedcount = length $ NonEmpty.filter ActiveLessonForUser.finished xs

getActiveLessonsForUser
  ∷ ∀ r db
  . MonadDB r db
  ⇒ Types.Key
  → db [Types.ActiveLessonForUser]
getActiveLessonsForUser user = query q (Only user)
  where

  q = [sql|
-- getActiveLessonsForUser
SELECT *
FROM ActiveLessonsForUser
WHERE User IS NULL OR User = ?;
|]

-- | Start a new lesson by randomly choosing the right number of
-- exercises and adding them to the users exercise list
startLesson
  :: MonadDB r db
  => Text      -- ^ Token
  -> Types.Key -- ^ Lesson name
  -- * Source- language and tree, target- langauge and tree.
  -> db Types.ExerciseLesson
startLesson token lesson = do
  user ← getUser token
  isRunning ← checkStarted user lesson
  if isRunning
  then continueLesson user lesson
  else newLesson      user lesson

checkStarted
  ∷ MonadDB r db
  ⇒ Types.Key -- ^ User
  → Types.Key -- ^ Lesson
  → db Bool
checkStarted user lesson
  =   (0 /=) . fromOnly . Unsafe.head
  <$> query @(Only Int) q (user,lesson)
  where
  q = [sql|
-- checkStarted
SELECT COUNT(*)
FROM StartedLesson
WHERE User = ?
  AND Lesson = ?;
|]

getUser ∷ MonadDB r db ⇒ Text → db Types.Key
getUser token = do
  xs ← query userQuery (Only token)
  case xs of
    []       → throwDbError NoUserFound
    [Only x] → pure x
    _        → throwDbError MultipleUsers
  where
  userQuery
    = [sql|
-- getuser
SELECT Id
FROM Session
WHERE Token = ?;
|]

class HasConnection v where
  giveConnection ∷ v → Connection

instance HasConnection Connection where
  giveConnection = identity

getConnection ∷ MonadDB r m ⇒ m Connection
getConnection = giveConnection <$> ask

-- | Like 'MonadError' but only for 'Error's.
class Monad m ⇒ MonadDatabaseError m where
  throwDbError ∷ Error → m a
  catchDbError ∷ m a → (Error → m a) → m a

instance MonadDatabaseError IO where
  throwDbError = throw
  catchDbError = catch

instance Monad m ⇒ MonadDatabaseError (ExceptT Error m) where
  throwDbError = throwError @Error
  catchDbError = catchError @Error

instance Monad m ⇒ MonadDatabaseError (DbT m) where
  throwDbError = DbT . throwError
  catchDbError (DbT act) h = DbT $ catchError act (unDbT . h)

type MonadDB r m =
  ( HasConnection r
  , MonadReader r m
  , MonadIO m
  , MonadDatabaseError m
  )

newtype DbT m a = DbT
  { unDbT ∷ (ReaderT Connection (ExceptT Error m)) a
  }

deriving newtype instance Functor m ⇒ Functor     (DbT m)
deriving newtype instance Monad m   ⇒ Applicative (DbT m)
deriving newtype instance Monad m   ⇒ Monad       (DbT m)
deriving newtype instance MonadIO m ⇒ MonadIO     (DbT m)
deriving newtype instance Monad m   ⇒ MonadReader Connection (DbT m)
deriving newtype instance Muste.MonadGrammar m ⇒ Muste.MonadGrammar (DbT m)

instance MonadTrans DbT where
  lift = DbT . lift . lift

type Db a = DbT IO a

-- instance

runDbT ∷ DbT m a -> Connection -> m (Either Error a)
runDbT (DbT db) c = runExceptT $ runReaderT db c

-- TODO Better maybe to switch to 'SQL.queryNamed'?
query
  ∷ ∀ res q r db
  . MonadDB r db
  ⇒ ToRow q
  ⇒ FromRow res
  ⇒ Query
  → q
  → db [res]
query qry q = do
  c ← getConnection
  wrapIoError $ SQL.query c qry q

query_
  :: ∀ res r db . MonadDB r db
  => FromRow res
  => Query -> db [res]
query_ qry = do
  c ← getConnection
  wrapIoError $ SQL.query_ c qry

execute
  ∷ MonadDB r db
  ⇒ ToRow q
  ⇒ Query
  → q
  → db ()
execute qry q = do
  c ← getConnection
  wrapIoError $ SQL.execute c qry q

executeMany
  ∷ MonadDB r db
  ⇒ ToRow q
  ⇒ Query
  → [q]
  → db ()
executeMany qry qs = do
  c ← getConnection
  wrapIoError $ SQL.executeMany c qry qs

-- | Wraps any io error in our application specific 'DriverError'
-- wrapper.
wrapIoError ∷ MonadDB r db ⇒ IO a → db a
wrapIoError io =
  liftIO (try io) >>= \case
  Left e  → throwDbError $ DriverError e
  Right a → pure a

shuffle :: MonadIO m => [a] -> m [a]
shuffle = liftIO . QC.generate . QC.shuffle

getTreePairs
  :: MonadDB r db
  => Types.Key
  -> db [Types.ExerciseLesson]
getTreePairs lesson = query q (Only lesson)
  where
  q = [sql|
-- getTreePairs
SELECT Exercise,
  Lesson,
  Name,
  SourceTree,
  TargetTree
FROM ExerciseLesson
WHERE Lesson = ?;
|]

newLesson
  :: MonadDB r db
  => Types.Key
  -> Types.Key
  -> db Types.ExerciseLesson
newLesson user lesson = do
  -- get exercise count
  -- Only count ← fromMaybe errNonUniqueLesson . listToMaybe
    -- <$> query @(Only Int) exerciseCountQuery (Only lesson)
  count ← getExerciseCount lesson
  -- get lesson round
  lessonRound ← getLessonRound user lesson
  selectedTrees ← do
    trees ← getTreePairs lesson
    -- randomly select
    take (fromInteger count) <$> shuffle trees
  exerciseLesson ← case selectedTrees of
    []      → throwDbError NoExercisesInLesson

    (x : _) → pure x

  -- save in database
  startLessonAux $ Types.StartedLesson lesson user lessonRound
  let
    step ∷ (Types.Numeric, Types.ExerciseLesson) → Types.ExerciseList
    step (round, Types.ExerciseLesson{..}) -- (exercise, _name, _, _)
      = Types.ExerciseList
      { user     = user
      , exercise = exercise
      , round    = round
      }
  insertExercises $ step <$> zip [lessonRound..] selectedTrees
  pure exerciseLesson

startLessonAux ∷ MonadDB r db ⇒ Types.StartedLesson → db ()
startLessonAux = execute [sql|
-- startLessonAux
INSERT INTO StartedLesson (Lesson, User, Round) VALUES (?,?,?);
|]

insertExercises ∷ MonadDB r db ⇒ [Types.ExerciseList] → db ()
insertExercises = executeMany [sql|
-- insertExercises
INSERT INTO ExerciseList (User,Exercise,Round) VALUES (?,?,?);
|]

getLessonRound
  ∷ MonadDB r db
  ⇒ Types.Key
  → Types.Key
  → db Integer
getLessonRound user lesson =
  fromOnly . Unsafe.head <$> query q (user,lesson)
  where
  q ∷ Query
  q = [sql|
-- getLessonRound
SELECT ifnull(MAX(FinishedExercise.Round) + 1,0)
FROM FinishedExercise
JOIN ExerciseList
    ON ExerciseList.Exercise = FinishedExercise.Exercise
JOIN Exercise ON ExerciseList.Exercise = Exercise.Id
WHERE
      FinishedExercise.User = ?
  -- Does this happen automatically if Lesson is null given the next
  -- condition?
  AND Lesson = ?;
|]

continueLesson
  ∷ MonadDB r db
  ⇒ Types.Key -- ^ Username
  → Types.Key -- ^ Lesson name
  → db Types.ExerciseLesson
continueLesson user lesson = do
  round ← getLessonRound user lesson
  getExercise lesson user round

finishExercise
  ∷ MonadDB r db
  ⇒ Text            -- ^ Token
  → Types.Key       -- ^ Lesson
  → Score           -- ^ Score
  → db ()
finishExercise token lesson score = do
  -- get user name
  user ← getUser token
  -- get lesson round
  round ← getLessonRound user lesson
  Types.ExerciseLesson{..} ← getExercise lesson user round
  finishExerciseAux $ Types.FinishedExercise
    { user     = user
    , exercise = exercise
    , score    = score
    , round    = round
    }
  -- check if all exercises finished
  finishedCount ← getFinishedExercises user exercise
  exerciseCount ← getExerciseCount lesson
  if finishedCount >= exerciseCount
  then do
    score ← getScore user lesson
    finishLesson $ Types.FinishedLesson
      { user   = user
      , lesson = lesson
      , score  = score
      , round  = succ round
      }
  else return ()

finishLesson
  ∷ MonadDB r db
  ⇒ Types.FinishedLesson -- ^ Lesson
  → db ()
finishLesson l@(Types.FinishedLesson{..}) = do
  execute q0 l
  execute q1 (user, lesson)
  where

  q0 = [sql|
-- finishLesson, q0
INSERT INTO FinishedLesson (Lesson, User, Score, Round) VALUES (?, ?, ?, ?);
|]

  q1 = [sql|
-- finishLesson, q1
DELETE
FROM StartedLesson
WHERE User = ?
  AND Lesson = ?;
|]

-- Gets an unfinished exercise
getExercise
  ∷ MonadDB r db
  ⇒ Types.Key     -- ^ Lesson
  → Types.Key     -- ^ User
  → Types.Numeric -- ^ Round
  → db Types.ExerciseLesson
getExercise lesson user round
  = fromMaybe errNoExercises . listToMaybe
    <$> query q (lesson,user,round)
  where

  q = [sql|
-- getExercise
SELECT
  Exercise.Id,
  Lesson.Id,
  Lesson.Name,
  SourceTree,
  TargetTree
FROM ExerciseList
JOIN Exercise ON Exercise = Exercise.Id
JOIN Lesson   ON Lesson   = Lesson.Id
WHERE Lesson = ?
  AND User   = ?
  AND ROUND  = ?
  AND (User, Exercise) NOT IN (
    SELECT User, Exercise
    FROM FinishedExercise
  );
|]
  errNoExercises = error "Database.continueLesson: Invariant violated: No exercises for lesson"

finishExerciseAux
  ∷ MonadDB r db
  ⇒ Types.FinishedExercise
  → db ()
finishExerciseAux = execute q
  where
  q = [sql|
-- finishExerciseAux
INSERT INTO FinishedExercise
  (User, Exercise, Score, Round)
VALUES (?,?,?,?);
|]

getFinishedExercises
  ∷ MonadDB r db
  ⇒ Types.Key -- ^ User
  → Types.Key -- ^ Exercise
  → db Types.Numeric
getFinishedExercises user lesson =
  fromOnly . Unsafe.head <$> query @(Only Integer) q (user,lesson)
  where
  q = [sql|
-- getFinishedExercises
SELECT COUNT(*)
FROM FinishedExercise F
WHERE User = ?
AND Exercise = ?;
|]

getExerciseCount
  ∷ MonadDB r db
  ⇒ Types.Key -- ^ Lesson
  → db Types.Numeric
getExerciseCount lesson =
  fromOnly . Unsafe.head <$> query @(Only Integer) q (Only lesson)
  where
  q = [sql|
-- getExerciseCount
SELECT ExerciseCount
FROM Lesson
WHERE Id = ?;
|]

-- | Get the score for the user and lesson.
getScore
  ∷ MonadDB r db
  ⇒ Types.Key -- ^ User
  → Types.Key -- ^ Lesson
  → db Score
getScore user lesson
  =   mconcat . fmap fromOnly
  <$> query @(Only Score) q (user, lesson)
  where

  q = [sql|
-- getScore
SELECT Score
FROM FinishedExercise
JOIN Exercise ON Exercise = Exercise.Id
WHERE User = ?
AND Lesson = ?;
|]

-- -- | The user and their score on each excercise.  If score and user is
-- -- null this means that /no/ user has completed the exercise.  If a
-- -- given exercise/user combination is not present in the output, then
-- -- this means that /this/ user has not completed the exercise.
-- getUserExerciseScores
--   ∷ MonadDB r db
--   ⇒ db [Types.UserExerciseScore]
-- getUserExerciseScores = query_
--   [sql|
--     SELECT
--       ExerciseLesson.Name,
--       ExerciseLesson.Lesson,
--       User,
--       Score
--     FROM ExerciseLesson
--     LEFT JOIN FinishedExercise
--       ON ExerciseLesson.Lesson = FinishedExercise.Lesson;
--   |]
