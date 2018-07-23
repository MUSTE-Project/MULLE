{-# language
    StandaloneDeriving
  , GeneralizedNewtypeDeriving
  , TypeOperators
  , LambdaCase
#-}
-- | One type per table
--
-- The reason I'm using type aliases is to inherit the `FromRow` and
-- `ToRow` instances defined for these types.
module Database.Types
  ( User
  , Session
  , Exercise
  , Lesson
  , FinishedExercise
  , StartedLesson
  , FinishedLesson
  , ExerciseList
  , TTree
  ) where

import Data.ByteString (ByteString)
import Data.Text (Text)

import Control.Exception (SomeException(..))
import Control.Monad.Fail
import Data.Time
import Database.SQLite.Simple (SQLData(..))
import Database.SQLite.Simple.Ok (Ok(..))
import Database.SQLite.Simple.FromField (FromField(..), fieldData, ResultError(..), returnError)
import Database.SQLite.Simple.ToField (ToField(..))
import Text.Read
import qualified Data.Text as T

import Muste (TTree)

type Blob = ByteString
type Numeric = Integer

parseNominalDiff :: Text -> Either String NominalDiffTime
parseNominalDiff = fmap fromInteger . readEither . T.unpack

instance MonadFail Ok where
  fail = Errors . pure . SomeException . ConversionFailed mempty mempty

instance FromField NominalDiffTime where
  fromField fld = case fieldData fld of
    (SQLText t) -> case parseNominalDiff t of
      Right tm -> pure tm
      Left e -> err ("couldn't parse UTCTime field: " ++ e)
    _ -> err "expecting SQLText column type"
    where
    err = returnError ConversionFailed fld

instance ToField NominalDiffTime where
  toField = SQLText . T.pack . show

type User =
  ( Text -- ^ @username@
  , Blob -- ^ @password@
  , Blob -- ^ @salt@
  , Bool -- ^ @enabled@
  )

type Session =
  ( Text -- ^ @user@
  , Text -- ^ @token@
  , UTCTime -- ^ @starttime@
  , UTCTime -- ^ @lastActive@
  )

-- Probably should be @(Blob, Blob, Text, Numeric)@
type Exercise =
  ( Text -- ^ @sourceTree@
  , Text -- ^ @targetTree@
  , Text -- ^ @lesson@
  , Numeric -- ^ @timeout@
  )

type Lesson =
  ( Text -- ^ @name@
  , Text -- ^ @description@
  , Text -- ^ @grammar@
  , Text -- ^ @sourceLanguage@
  , Text -- ^ @targetLanguage@
  , Numeric -- ^ @exerciseCount@
  , Bool -- ^ @enabled@
  , Bool -- ^ @repeatable@
  )

type FinishedExercise =
  ( Text -- ^ @user@
  , Text -- ^ @sourceTree@
  , Text -- ^ @targetTree@
  , Text -- ^ @lesson@
  , Numeric -- ^ @time@
  , Numeric -- ^ @clickCount@
  , Numeric -- ^ @round@
  )

type StartedLesson =
  ( Text -- ^ @lesson@
  , Text -- ^ @user@
  , Numeric -- ^ @round@
  )

type FinishedLesson =
  ( Text -- ^ @lesson@
  , Text -- ^ @user@
  , Numeric -- ^ @time@
  , Numeric -- ^ @clickCount@
  , Numeric -- ^ @round@
  )

type ExerciseList =
  ( Text -- ^ @user@
  , Text -- ^ @sourceTree@
  , Text -- ^ @targetTree@
  , Text -- ^ @lesson@
  , Numeric -- ^ @round@
  )
