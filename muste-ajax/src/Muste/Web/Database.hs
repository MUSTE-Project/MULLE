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
import qualified Muste.Web.Database.Types as ActiveLesson0 (ActiveLesson0(..))
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
getLessons = query_ [sql|select * from lesson;|]

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
  execute [sql|INSERT INTO User VALUES (?,?,?,?);|] u `catchDbError` h
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

-- | Removes an existing user from the database.
rmUser
  ∷ MonadDB r db
  ⇒ Text
  → db ()
rmUser nm
  = void
  $ execute [sql|DELETE FROM User WHERE Username = ?;|]
  (Only nm)

authUser
  :: MonadDB r db
  => Text -- ^ Username
  -> Text -- ^ Password
  -> db ()
authUser user pass = do
  -- Get password and salt from database
  userList <- query @(ByteString, ByteString, Bool) selectPasswordSaltQuery [user]
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
  selectPasswordSaltQuery
    = [sql|SELECT Password,Salt,Enabled FROM User WHERE (Username = ?);|]

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
  :: MonadDB r db
  => Text -- ^ Username
  -> db Types.Session
createSession user = do
    -- maybe check for old sessions and clean up?
    let deleteSessionQuery = [sql|DELETE FROM Session WHERE User = ? ;|] :: Query
    execute deleteSessionQuery [user]
    -- create new session
    timeStamp <- getCurrentTime
    let
      sessionData ∷ ByteString
      sessionData = convertString $ formatTime timeStamp
      token ∷ Text
      token = convertString (show (hash @ByteString @SHA3_512 sessionData))
    pure $ Types.Session user token timeStamp timeStamp

-- | Creates a new session and returns the session token.  At the
-- moment overly simplified.
startSession
  :: MonadDB r db
  => Text -- ^ Username
  -> db Text
startSession user = do
  session@(Types.Session _ token _ _) <- createSession user
  let insertSessionQuery = [sql|INSERT INTO Session VALUES (?,?,?,?);|]
  execute insertSessionQuery session
  return token

formatTime ∷ UTCTime → String
formatTime = Time.formatTime Time.defaultTimeLocale "%s"

updateActivity :: MonadDB r db ⇒ Text -> db ()
updateActivity token = do
  -- We should use to- from- row instances for UTCTime in stead.
  timeStamp ← formatTime <$> getCurrentTime
  let updateSessionLastActiveQuery = [sql|UPDATE Session SET LastActive = ? WHERE Token = ?;|]
  execute updateSessionLastActiveQuery (timeStamp,token)

-- | Returns @Just err@ if there is an error.
verifySession
  :: MonadDB r db
  => Text -- ^ Token
  -> db ()
verifySession token = do
  -- Get potential user session(s)
  let selectSessionQuery = [sql|SELECT LastActive FROM Session WHERE Token = ?;|]
  sessions <- query @(Only UTCTime) selectSessionQuery [token]
  -- from here might not be executed due to lazy evaluation...
  -- Compute the difference in time stamps
  newTimeStamp <- getCurrentTime
  let oldTimeStamp = fromOnly . Unsafe.head $ sessions
      deleteSessionQuery = [sql|DELETE FROM Session WHERE Token = ? ;|]
      diff = Time.diffUTCTime newTimeStamp oldTimeStamp
      hour = fromInteger 60
      threshold = fromInteger (30 * hour)
      error
        | length sessions  == 0 = NoCurrentSession
        | diff > threshold      = SessionTimeout
        | otherwise             = MultipleSessions
  -- ... until here. check if a session exists and it is has been active in the last 30 minutes
  if length sessions == 1 && diff <= threshold
  then pure ()
  else do
    execute deleteSessionQuery [token]
    throwDbError error

-- | List all the lessons i.e. lesson name, description and exercise
-- count
getActiveLessons
  ∷ ∀ r db
  . MonadDB r db
  ⇒ Text -- Token
  → db [Types.ActiveLesson]
getActiveLessons token = do
  user <- getUser token
  fmap step . groupOn ActiveLesson0.name <$> getActiveLessonsForUser user
  where
  step ∷ (NonEmpty Types.ActiveLesson0) → Types.ActiveLesson
  step xs@(Types.ActiveLesson0{..} :| _) = Types.ActiveLesson
    { name          = name
    , description   = description
    , exercisecount = exercisecount
    , score         = foldMap (SQL.runNullable . ActiveLesson0.score) xs
    , finished      = finished
    , enabled       = enabled
    , passedcount   = NonEmpty.length xs
    }

getActiveLessonsForUser
  ∷ ∀ r db
  . MonadDB r db
  ⇒ Text
  → db [Types.ActiveLesson0]
getActiveLessonsForUser user =
  query
    [sql|
      SELECT
        Name,
        Description,
        ExerciseCount,
        Score,
        Finished,
        Enabled
      FROM ActiveLesson
      WHERE
        User IS NULL
        OR User = ?;
    |] (Only user)

-- | Start a new lesson by randomly choosing the right number of
-- exercises and adding them to the users exercise list
startLesson
  :: MonadDB r db
  => Text -- ^ Token
  -> Text -- ^ Lesson name
  -- * Source- language and tree, target- langauge and tree.
  -> db (Text, Types.Unannotated, Text, Types.Unannotated)
startLesson token lesson = do
  user ← getUser token
  isRunning <- checkStarted user lesson
  if isRunning
  then continueLesson user lesson
  else newLesson      user lesson

checkStarted
  ∷ MonadDB r db
  ⇒ Text -- ^ User
  → Text -- ^ Lesson
  → db Bool
checkStarted user lesson
  =   (0 /=) . fromOnly . Unsafe.head
  <$> query @(Only Int) q (user,lesson)
  where
  q = [sql|SELECT COUNT(*) FROM StartedLesson WHERE User = ? AND Lesson = ?|]

getUser ∷ MonadDB r db ⇒ Text → db Text
getUser token = do
  xs ← query userQuery (Only token)
  case xs of
    []       → throwDbError NoUserFound
    [Only x] → pure x
    _        → throwDbError MultipleUsers
  where
  userQuery
    = [sql|SELECT User FROM Session WHERE Token = ?;|]

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
  => Text
  -> db [(Types.Unannotated, Types.Unannotated)]
getTreePairs lesson = query exerciseQuery (Only lesson)
  where
  exerciseQuery =
    [sql| SELECT SourceTree, TargetTree
          FROM Exercise
          WHERE Lesson = ?;|]

newLesson
  :: MonadDB r db
  => Text
  -> Text
  -> db (Text, Types.Unannotated, Text, Types.Unannotated)
newLesson user lesson = do
  -- get exercise count
  -- Only count ← fromMaybe errNonUniqueLesson . listToMaybe
    -- <$> query @(Only Int) exerciseCountQuery (Only lesson)
  Only count ← query @(Only Int) exerciseCountQuery (Only lesson)
    >>= \case
      []    → throwDbError NonUniqueLesson
      (x:_) → pure x
  -- get lesson round
  round <- getLessonRound user lesson
  trees <- getTreePairs lesson
  -- randomly select
  selectedTrees <- take count <$> shuffle trees
  (src,trg) ← case selectedTrees of
    []      → throwDbError NoExercisesInLesson

    (x : _) → pure x

  -- save in database
  let startedLesson :: Types.StartedLesson
      startedLesson = Types.StartedLesson lesson user (succ round)
  execute insertStartedLesson startedLesson
  let
    step ∷ (Types.Unannotated, Types.Unannotated) → Types.ExerciseList
    step (src, trg)
      = Types.ExerciseList
      { user
      , lesson
      , sourceSentence = src
      , targetSentence = trg
      , round = round
      }
  executeMany @_ @_ @Types.ExerciseList insertExerciseList $ step <$> selectedTrees
  (sourceLang, targetLang) <- getLangs lesson
  pure (sourceLang, src, targetLang, trg)
  where
  exerciseCountQuery =
    [sql|
      SELECT ExerciseCount FROM Lesson WHERE Name = ?;
    |]
  insertStartedLesson =
    [sql|
      INSERT INTO StartedLesson (Lesson, User, Round)
      VALUES (?,?,?);
    |]
  insertExerciseList =
    [sql|
      INSERT INTO ExerciseList (User,Lesson,SourceTree,TargetTree,Round)
      VALUES (?,?,?,?,?);
    |]

getLangs :: MonadDB r db => Text -> db (Text, Text)
getLangs lesson = do
  langs <- query @_ @_ languagesQuery (Only lesson)
  case langs of
    [(a, b)] -> pure (a, b)
    _        -> throw LangNotFound
  where
  languagesQuery :: Query
  languagesQuery
    = [sql|SELECT SourceLanguage, TargetLanguage FROM Lesson WHERE Name = ?;|]

getLessonRound ∷ MonadDB r db ⇒ Text → Text → db Integer
getLessonRound user lesson = do
  [Only round] <- query lessonRoundQuery (user,lesson)
  pure round
  where
  lessonRoundQuery ∷ Query
  lessonRoundQuery = [sql|SELECT ifnull(MAX(Round),0) FROM FinishedExercise WHERE User = ? AND Lesson = ?;|]

continueLesson
  :: MonadDB r db
  => Text -- ^ Username
  -> Text -- ^ Lesson name
  -> db (Text, Types.Unannotated, Text, Types.Unannotated)
continueLesson user lesson = do
  round <- getLessonRound user lesson
  (sourceTree,targetTree) <- fromMaybe errNoExercises . listToMaybe
    <$> query @(Types.Unannotated, Types.Unannotated)
        selectExerciseListQuery (lesson,user,round)
  (sourceLang,targetLang) <- getLangs lesson
  pure (sourceLang,sourceTree,targetLang,targetTree)
  where
  selectExerciseListQuery = [sql|
       SELECT SourceTree,TargetTree FROM ExerciseList
       WHERE Lesson = ? AND User = ?
       AND (User,SourceTree,TargetTree,Lesson) NOT IN
       (SELECT User,SourceTree,TargetTree,Lesson
       FROM FinishedExercise WHERE Round = ?);|]
  errNoExercises = error "Database.continueLesson: Invariant violated: No exercises for lesson"

finishExercise
  ∷ MonadDB r db
  ⇒ Text            -- ^ Token
  → Text            -- ^ Lesson
  → Score           -- ^ Score
  → db ()
finishExercise token lesson score = do
  -- get user name
  user ← getUser token
  -- get lesson round
  [Only round] <- query @(Only Integer) lessonRoundQuery (user,lesson)
  ((sourceSentence,targetSentence):_)
    <- query selectExerciseListQuery (lesson,user,round)
  execute insertFinishedExerciseQuery
    $ Types.FinishedExercise
      { user
      , lesson
      , sourceSentence
      , targetSentence
      , score
      , round
      }
  -- check if all exercises finished
  finishedCount ← getFinishedExercises user lesson
  exerciseCount ← getExerciseCount lesson
  if finishedCount >= exerciseCount
  then do
    score ← getScore user lesson
    round ← getCurrentRound user lesson
    execute insertFinishedLessonQuery (user, lesson, score, round)
    execute deleteStartedLessonQuery (user, lesson)
  else return ()
  where
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
        (User,Lesson,SourceTree,TargetTree,Score,Round)
      VALUES (?,?,?,?,?,?);
      |]
    deleteStartedLessonQuery = [sql|
      DELETE FROM StartedLesson
      WHERE User = ? AND Lesson = ? ;
      |]
    insertFinishedLessonQuery = [sql|
      INSERT INTO FinishedLesson (User,Lesson,Score,Round) VALUES (?, ?, ?, ?);
      |]

getFinishedExercises
  ∷ MonadDB r db
  ⇒ Text -- ^ User
  → Text -- ^ Lesson
  → db Types.Numeric
getFinishedExercises user lesson =
  fromOnly . Unsafe.head <$> query @(Only Integer) countFinishesExercisesQuery (user,lesson)
  where
  countFinishesExercisesQuery
    = [sql|
      SELECT COUNT(*)
      FROM FinishedExercise F
      WHERE User = ?
      AND Lesson = ?
    |]

getExerciseCount
  ∷ MonadDB r db
  ⇒ Text -- ^ Lesson
  → db Types.Numeric
getExerciseCount lesson =
  fromOnly . Unsafe.head <$> query @(Only Integer) countExercisesInLesson (Only lesson)
  where
  countExercisesInLesson = [sql|
    SELECT ExerciseCount FROM Lesson WHERE Name = ?;
    |]

endSession :: MonadDB r db ⇒ Text -> db ()
endSession token = do
  let deleteSessionQuery = [sql|DELETE FROM Session WHERE Token = ?;|]
  execute deleteSessionQuery [token]

getCurrentRound
  ∷ MonadDB r db
  ⇒ Text -- ^ User
  → Text -- ^ Lesson
  → db (Maybe Types.Numeric)
getCurrentRound user lesson =
  fromOnly . Unsafe.head <$> query
    [sql|
        SELECT MAX(Round)
        FROM StartedLesson
        WHERE User = ?
        AND Lesson = ?
    |] (user, lesson)

-- TODO Stub
-- | Get the score for the user and lesson.
getScore
  ∷ MonadDB r db
  ⇒ Text -- ^ User
  → Text -- ^ Lesson
  → db Score
getScore user lesson = mconcat . fmap fromOnly <$> query @(Only Score)
  [sql|
      SELECT Score
      FROM FinishedExercise
      WHERE User = ?
      AND Lesson = ?
  |] (user, lesson)
