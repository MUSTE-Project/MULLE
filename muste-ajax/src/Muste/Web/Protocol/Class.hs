-- | Defines the inner workings of the api handler.
--
-- Module      : Muste.Web.Protocol.Class
-- License     : Artistic License 2.0
-- Stability   : experimental
-- Portability : POSIX
--
-- This module defines api-specific behaviour in the form of the
-- 'ProtocolT' monad transformer.  Requests are made to the server in
-- the form of ajax requests.  Errors thrown, for whatever reason, are
-- reported via HTTP status codes. Additional information are provided
-- via a json formatted response.

{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language
 ConstraintKinds,
 DeriveAnyClass,
 DerivingStrategies,
 FlexibleContexts,
 GADTs,
 GeneralizedNewtypeDeriving,
 LambdaCase,
 MultiParamTypeClasses,
 OverloadedLists,
 OverloadedStrings,
 RecordWildCards,
 ScopedTypeVariables,
 StandaloneDeriving,
 TypeApplications,
 UndecidableInstances
#-}

module Muste.Web.Protocol.Class
  ( MonadProtocol
  , ProtocolT
  , runProtocolT
  , AppState(..)
  , HttpStatus(..)
  , Response(..)
  , ProtocolError(..)
  , ApiError(..)
  , Reason(..)
  , Contexts
  ) where

import           Prelude ()
import           Muste.Prelude

import           Database.SQLite.Simple (Connection)

import           Control.Monad.Base (MonadBase)
import           Control.Monad.Trans.Control (MonadBaseControl)
import           Data.Aeson
import           Data.ByteString (ByteString)
import           Data.Map (Map)
import           Data.Vector (Vector)
import qualified Snap
import           Snap (MonadSnap)
import qualified Data.List as List

import           Muste.Linearization (Context)
import qualified Muste.Sentence      as Sentence
import qualified Muste.Grammar       as Grammar

import qualified Muste.Web.Database  as Database
import           Muste.Web.Database (MonadDatabaseError(..))

-- | Maps a lesson to a map from grammars(-identifiers) to their
-- corresponding contexts.
type Contexts = Map Text (Map Sentence.Language Context)

-- | The state that the server will have throughout the uptime.
data AppState = AppState
  { connection    :: Connection
  , contexts      :: Contexts
  , knownGrammars :: Grammar.KnownGrammars
  , lessonsCfg    :: FilePath
  }

instance Grammar.HasKnownGrammars AppState where
  giveKnownGrammars = knownGrammars

-- | A simple monad transformer for handling responding to requests.
newtype ProtocolT m a = ProtocolT
  { unProtocolT :: ExceptT ProtocolError m a
  }

deriving newtype instance Functor m      => Functor      (ProtocolT m)
deriving newtype instance Monad m        => Applicative  (ProtocolT m)
deriving newtype instance Monad m        => Monad        (ProtocolT m)
deriving newtype instance MonadIO m      => MonadIO      (ProtocolT m)
deriving newtype instance MonadBaseControl IO m => MonadBaseControl IO (ProtocolT m)
deriving newtype instance MonadBase IO m => MonadBase IO (ProtocolT m)
deriving newtype instance MonadReader AppState m => MonadReader AppState (ProtocolT m)
deriving newtype instance MonadPlus m    => MonadPlus    (ProtocolT m)
deriving newtype instance Monad m        => Alternative  (ProtocolT m)
deriving newtype instance MonadSnap m    => MonadSnap    (ProtocolT m)
deriving newtype instance Monad m        => MonadError ProtocolError (ProtocolT m)
deriving newtype instance Grammar.MonadGrammar m => Grammar.MonadGrammar (ProtocolT m)

instance Monad m => MonadDatabaseError (ProtocolT m) where
  throwDbError = ProtocolT . throwError . DatabaseError
  -- | Only handles the database error.
  catchDbError (ProtocolT act) h
    = ProtocolT $ catchError act (unProtocolT . h')
    where
    -- The "demoted" handler.
    h' = \case
      DatabaseError err -> h err
      e                 -> ProtocolT $ throwError e

data ProtocolError
  -- 'UnspecifiedError' is needed to make this a monoid to in turn
  -- make ProtocolT a monadplus as requested by monadsnap.  Don't use
  -- this!  Better to use 'SomeProtocolError' or even better, add a
  -- constructor.
  = UnspecifiedError
  | DatabaseError Database.Error
  | ProtocolApiError ApiError
  | forall e . Exception e => SomeProtocolError e

instance Semigroup ProtocolError where
  a <> _ = a

instance Monoid ProtocolError where
  mempty = UnspecifiedError

deriving stock instance Show ProtocolError

instance Exception ProtocolError where
  displayException = \case
    UnspecifiedError    -> "Some unspecified error occured"
    DatabaseError err   -> "A database error occurred: " <> displayException err
    SomeProtocolError e -> displayException e
    ProtocolApiError e  -> displayException e

data ApiError
  = MissingApiRoute String
  | NoAccessToken
  | BadRequest
  | SessionInvalid
  | LoginFail
  | ErrReadBody
  | DecodeError String
  | LessonNotFound Text
  | LanguageNotFound Sentence.Language

deriving stock instance Show ApiError

instance Exception ApiError where
  displayException = \case
    MissingApiRoute s   -> printf "missing api route for `%s`" s
    NoAccessToken       -> "No cookie found"
    SessionInvalid      -> "Session invalid, please log in again"
    BadRequest          -> "Bad request!"
    LoginFail           -> "Login failure"
    ErrReadBody         -> "Error reading request body."
    DecodeError s       -> printf "Error decoding JSON: %s" s
    LessonNotFound l    -> printf "Lesson not found %s" (convertString @_ @String l)
    LanguageNotFound l  -> printf "Language not found %s" (show l)

newtype ErrorIdentifier = ErrorIdentifier (Vector Int)

deriving newtype instance IsList ErrorIdentifier
instance ToJSON ErrorIdentifier where
  toJSON (ErrorIdentifier v)
    = toJSON @String $ List.intercalate "-" $ map show $ toList v
deriving newtype instance Semigroup ErrorIdentifier

-- There might be better ways of handling this I suppose...  Another
-- idea would be to generate a tree (since errors can be nested).
-- | Application specific unique error code for responses.
class HasErrorIdentifier a where
  errorIdentifier :: a -> ErrorIdentifier
  errorResponseCode :: a -> HttpStatus

instance HasErrorIdentifier ProtocolError where
  errorIdentifier = \case
    UnspecifiedError    -> [0]
    SomeProtocolError{} -> [1]
    DatabaseError e     -> [2] <> errorIdentifier e
    ProtocolApiError e  -> [3] <> errorIdentifier e
  errorResponseCode = \case
    UnspecifiedError    -> 500
    SomeProtocolError{} -> 500
    DatabaseError e     -> errorResponseCode e
    ProtocolApiError e  -> errorResponseCode e

instance HasErrorIdentifier ApiError where
  errorIdentifier = fromList . pure . \case
    MissingApiRoute{}  -> 0
    NoAccessToken      -> 1
    SessionInvalid     -> 2
    BadRequest         -> 3
    LoginFail          -> 4
    ErrReadBody        -> 5
    DecodeError{}      -> 6
    LessonNotFound{}   -> 7
    LanguageNotFound{} -> 8
  errorResponseCode = \case
    MissingApiRoute{}  -> 501
    NoAccessToken      -> 401
    SessionInvalid     -> 400
    BadRequest         -> 400
    LoginFail          -> 401
    ErrReadBody        -> 400
    DecodeError{}      -> 400
    LessonNotFound{}   -> 400
    LanguageNotFound{} -> 400


instance HasErrorIdentifier Database.Error where
  errorIdentifier = fromList . pure . \case
    Database.NoUserFound               -> 0
    Database.LangNotFound              -> 1
    Database.MultipleUsers             -> 2
    Database.NotCurrentSession         -> 3
    Database.SessionTimeout            -> 4
    Database.MultipleSessions          -> 5
    Database.NoExercisesInLesson       -> 6
    Database.NonUniqueLesson           -> 7
    Database.NotAuthenticated          -> 8
    Database.DriverError{}             -> 9
    Database.UserAlreadyExists         -> 10
    Database.NoActiveExercisesInLesson -> 11
    Database.LessonAlreadySolved       -> 12
  errorResponseCode = \case
    Database.NoUserFound               -> 401
    Database.LangNotFound              -> 400
    Database.MultipleUsers             -> 401
    Database.NotCurrentSession         -> 401
    Database.SessionTimeout            -> 401
    Database.MultipleSessions          -> 401
    Database.NoExercisesInLesson       -> 400
    Database.NonUniqueLesson           -> 400
    Database.NotAuthenticated          -> 401
    Database.DriverError{}             -> 500
    -- Not quite sure what is the right option here.
    Database.UserAlreadyExists         -> 400
    Database.NoActiveExercisesInLesson -> 400
    Database.LessonAlreadySolved       -> 400

instance ToJSON ProtocolError where
  toJSON err = object
    [ "error" .= object
      [ "message" .= displayException err
      , "id"      .= errorIdentifier err
      ]
    ]

type MonadProtocol m =
  ( MonadReader AppState m
  , MonadIO m
  , Database.MonadDatabaseError m
  , MonadError ProtocolError m
  , MonadSnap m
  , Grammar.MonadGrammar m
  )

instance Database.HasConnection AppState where
  giveConnection = connection

-- Not all response codes are mapped in `snap`.
data Reason = UnprocessableEntity

displayReason :: Reason -> ByteString
displayReason = \case
  UnprocessableEntity -> "Unprocessable Entity"

data HttpStatus = Code Int | CodeReason Int Reason

instance Num HttpStatus where
  fromInteger = Code . fromInteger
  (+) = cheatNumErr
  (*) = cheatNumErr
  abs = cheatNumErr
  signum = cheatNumErr
  negate = cheatNumErr

cheatNumErr :: a
cheatNumErr = error "Don't use the num instance of HttpStatus for anything other than fromInteger"

setResponseCode :: HttpStatus -> Snap.Response -> Snap.Response
setResponseCode s = case s of
  Code n -> Snap.setResponseCode n
  CodeReason n r -> Snap.setResponseStatus n (displayReason r)

data Response a = Response
  { body   :: a
  , status :: Maybe HttpStatus
  }

instance Functor Response where
  fmap f (Response b s) = Response (f b) s

instance Applicative Response where
  Response f0 b0 <*> Response a1 b1 = Response (f0 a1) (b0 *> b1)
  pure a = Response a Nothing

instance Semigroup a => Semigroup (Response a) where
  Response a0 b0 <> Response a1 b1 = Response (a0 <> a1) (b0 *> b1)

instance Monoid a => Monoid (Response a) where
  mempty = Response mempty Nothing

-- | Errors are returned as JSON responses.
runProtocolT :: MonadSnap m => ToJSON a => ProtocolT m (Response a) -> m ()
runProtocolT app = do
  Snap.modifyResponse (Snap.setContentType "application/json")
  res  <- runExceptT $ unProtocolT app
  case res of
    Left err -> do
       Snap.modifyResponse . setResponseCode . errorResponseCode $ err
       Snap.writeLBS $ encode err
    Right resp -> respond resp

respond :: MonadSnap m => ToJSON a => Response a -> m ()
respond Response{..} = Snap.writeLBS $ encode body
