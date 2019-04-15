-- | Monad for accessing the database.
--
-- Module      : Muste.Web.Database.Class
-- License     : Artistic License 2.0
-- Stability   : experimental
-- Portability : POSIX

{-# OPTIONS_GHC -Wall #-}
{-# Language
 ConstraintKinds,
 DeriveAnyClass,
 DerivingStrategies,
 FlexibleInstances,
 GeneralizedNewtypeDeriving,
 MultiParamTypeClasses,
 NamedFieldPuns,
 RecordWildCards,
 StandaloneDeriving,
 TypeApplications
#-}

module Muste.Web.Database.Class
  ( MonadDB
  , DbT(DbT)
  , Db
  , HasConnection(..)
  , getConnection
  , Error(..)
  , MonadDatabaseError(..)
  , queryNamed
  , executeNamed
  , runDbT
  , query_
  , executeManyNamed
  ) where

import Control.Exception (Exception(displayException), SomeException, try, throw, catch)
import Control.Monad.Except (ExceptT, throwError, runExceptT, catchError)
import Control.Monad.Reader

import Database.SQLite.Simple (Query, Connection, FromRow, NamedParam)
import qualified Database.SQLite.Simple as SQL

import qualified Muste


data Error
  = NoUserFound
  | LangNotFound
  | MultipleUsers
  | NotCurrentSession
  | SessionTimeout
  | MultipleSessions
  | NoExercisesInLesson
  | NonUniqueLesson
  | NotAuthenticated
  | DriverError SomeException
  | UserAlreadyExists
  | NoActiveExercisesInLesson
  | LessonAlreadySolved

deriving stock instance Show Error
instance Exception Error where
  displayException err = case err of
    NoUserFound         -> "No user found."
    LangNotFound        -> "Could not find the languages."
    MultipleUsers
      ->  "Well this is embarrasing.  "
      <> "It would appear that someone managed "
      <> "to steal youre identity."
    NotCurrentSession   -> "Not current session"
    SessionTimeout      -> "Session timeout"
    MultipleSessions    -> "More than one session"
    NoExercisesInLesson -> "No exercises for lesson"
    NoActiveExercisesInLesson -> "No unsolved exercises for lesson"
    NonUniqueLesson     -> "Non unique lesson"
    NotAuthenticated    -> "User is not authenticated"
    DriverError e
      ->  "Unhandled driver error: "
      <> displayException e
    UserAlreadyExists -> "The username is taken"
    LessonAlreadySolved -> "This lesson has already been solved.  You cannot restart it!"

class HasConnection v where
  giveConnection :: v -> Connection

instance HasConnection Connection where
  giveConnection = \x -> x

getConnection :: MonadDB r m => m Connection
getConnection = giveConnection <$> ask

-- | Like 'MonadError' but only for 'Error's.
class Monad m => MonadDatabaseError m where
  throwDbError :: Error -> m a
  catchDbError :: m a -> (Error -> m a) -> m a

instance MonadDatabaseError IO where
  throwDbError = throw
  catchDbError = catch

instance Monad m => MonadDatabaseError (ExceptT Error m) where
  throwDbError = throwError @Error
  catchDbError = catchError @Error

instance Monad m => MonadDatabaseError (DbT m) where
  throwDbError = DbT . throwError
  catchDbError (DbT act) h = DbT $ catchError act (unDbT . h)

type MonadDB r m =
  ( HasConnection r
  , MonadReader r m
  , MonadIO m
  , MonadDatabaseError m
  )

newtype DbT m a = DbT
  { unDbT :: (ReaderT Connection (ExceptT Error m)) a
  }

deriving newtype instance Functor m => Functor     (DbT m)
deriving newtype instance Monad m   => Applicative (DbT m)
deriving newtype instance Monad m   => Monad       (DbT m)
deriving newtype instance MonadIO m => MonadIO     (DbT m)
deriving newtype instance Monad m   => MonadReader Connection (DbT m)
deriving newtype instance Muste.MonadGrammar m => Muste.MonadGrammar (DbT m)

instance MonadTrans DbT where
  lift = DbT . lift . lift

type Db a = DbT IO a

runDbT :: DbT m a -> Connection -> m (Either Error a)
runDbT (DbT db) c = runExceptT $ runReaderT db c

query_
  :: MonadDB r db
  => FromRow res
  => Query -> db [res]
query_ qry = wrappedWithCon $ \c ->
  SQL.query_ c qry

queryNamed
  :: MonadDB r db
  => FromRow res
  => Query
  -> [NamedParam]
  -> db [res]
queryNamed q a = wrappedWithCon $ \c ->
  SQL.queryNamed c q a

executeNamed
  :: MonadDB r db
  => Query
  -> [NamedParam]
  -> db ()
executeNamed q a = wrappedWithCon $ \c ->
  SQL.executeNamed c q a

-- This /may/ not be as efficient as using 'SQL.executeMany', but
-- unfortunately they do not exposed a version of that wih named
-- params.
executeManyNamed
  :: MonadDB r db
  => Query
  -> [[NamedParam]]
  -> db ()
executeManyNamed q xs = wrappedWithCon $ \c ->
  void $ traverse (SQL.executeNamed c q) xs

wrappedWithCon :: MonadDB r db => (Connection -> IO a) -> db a
wrappedWithCon act = do
  c <- getConnection
  wrapIoError $ act c

-- | Wraps any io error in our application specific 'DriverError'
-- wrapper.
wrapIoError :: MonadDB r db => IO a -> db a
wrapIoError io =
  do result <- liftIO (try io)
     case result of
       Left e  -> throwDbError $ DriverError e
       Right a -> pure a
