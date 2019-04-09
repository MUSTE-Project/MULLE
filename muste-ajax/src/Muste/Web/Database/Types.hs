-- | Defines types corresponding to the data in the tables/views of
-- the database.
--
-- Module      : Muste.Web.Database.Types
-- License     : Artistic License 2.0
-- Stability   : experimental
-- Portability : POSIX
--
-- Some of the types are direct translations, some are not.
--
-- Many of the types are very similar to the ones defined in
-- "Muste.Web.Ajax".  This is intentional. The reason for this is that
-- SQL database are row-orientend whereas JSON is document oriented.

{-# OPTIONS_GHC -Wall #-}
{-# Language
 LambdaCase,
 DeriveAnyClass,
 DeriveGeneric,
 DerivingStrategies,
 DuplicateRecordFields,
 GeneralizedNewtypeDeriving,
 RecordWildCards,
 StandaloneDeriving,
 TypeApplications,
 TypeOperators
#-}

module Muste.Web.Database.Types
  ( User(..)
  , CreateUser(..)
  , ChangePassword(..)
  , Session(..)
  , Exercise(..)
  , Lesson(..)
  , StartedLesson(..)
  , FinishedLesson(..)
  , ExerciseList(..)
  , ActiveLessonForUser(..)
  , UserLessonScore(..)
  , Key(..)
  , TTree
  , Sentence.Unannotated
  , Blob(..)
  , Numeric(..)
  , ExerciseLesson(..)
  , Direction(..)
  , Token(..)
  ) where

import Prelude ()
import Muste.Prelude

import Database.SQLite.Simple (FromRow(..), ToRow(..))
import Database.SQLite.Simple.ToField (ToField(..))
import Database.SQLite.Simple.FromField (FromField(..))

import Data.Int (Int64)
import Data.ByteString (ByteString)
import Data.Aeson (FromJSON(..), ToJSON(..))
import qualified Data.Aeson as Aeson

import Muste.Tree (TTree)
import qualified Muste.Sentence.Unannotated as Sentence (Unannotated)
import Muste.Sentence.Unannotated (Unannotated)

import Muste.Web.Types.Score (Score)

import Database.SQLite.Simple.FromRow.Generic

newtype Blob = Blob { unBlob :: ByteString }

deriving stock   instance Show      Blob
deriving newtype instance Eq        Blob
deriving newtype instance ToField   Blob
deriving newtype instance FromField Blob

-- | The sql driver we use uses 64 bit integers meaning that we
-- anyways convert to and from this.  sqlite3s documentation has this to say:
--
-- > INTEGER. The value is a signed integer, stored in 1, 2, 3, 4, 6,
-- > or 8 bytes depending on the magnitude of the value.
newtype Numeric = Numeric { unNumeric :: Int64 }

deriving stock   instance Show      Numeric
deriving newtype instance Eq        Numeric
deriving newtype instance Ord       Numeric
deriving newtype instance Num       Numeric
deriving newtype instance Real      Numeric
deriving newtype instance Enum      Numeric
deriving newtype instance Integral  Numeric
deriving newtype instance ToField   Numeric
deriving newtype instance FromField Numeric
deriving newtype instance ToJSON    Numeric
deriving newtype instance FromJSON  Numeric

-- | Identified keys.
data Key a = Key { unKey :: Int64 }

deriving stock instance Show (Key a)
deriving stock instance Eq (Key a)
instance ToField   (Key a) where
  toField = toField . unKey
instance FromField (Key a) where
  fromField = fmap Key . fromField
instance ToJSON    (Key a) where
  toJSON = toJSON . unKey
instance FromJSON  (Key a) where
  parseJSON = fmap Key . parseJSON

data User = User
  { name                :: Text
  , password            :: Blob
  , salt                :: Blob
  , enabled             :: Bool
  }

deriving stock    instance Show    User
deriving stock    instance Generic User
instance ToRow User where
   toRow = genericToRow
instance FromRow User where
   fromRow = genericFromRow

data CreateUser = CreateUser
  { name     :: Text
  , password :: Text
  , enabled  :: Bool
  }

deriving stock    instance Show    CreateUser
deriving stock    instance Generic CreateUser
instance ToRow CreateUser where
   toRow = genericToRow
instance FromRow CreateUser where
   fromRow = genericFromRow

-- If we made it so that only /already/ authenticated users could
-- change their password, then we ought to change to a user id here in
-- stead of their name.
data ChangePassword = ChangePassword
  { name        :: Text
  , oldPassword :: Text
  , newPassword :: Text
  }

deriving stock    instance Show    ChangePassword
deriving stock    instance Generic ChangePassword
instance ToRow ChangePassword where
   toRow = genericToRow
instance FromRow ChangePassword where
   fromRow = genericFromRow

newtype Token = Token Text

deriving stock    instance Show      Token
deriving stock    instance Generic   Token
deriving newtype  instance ToField   Token
deriving newtype  instance FromField Token

instance FromJSON Token where
  parseJSON = Aeson.withText "Token" $ \s -> return (Token s)

instance ToJSON Token where
  toJSON (Token token) = Aeson.String token


-- NB Missing the key to be exactly the same as the stuff in the db.
data Session = Session
  { user                :: Text
  , token               :: Token
  , startTime           :: UTCTime
  , lastActive          :: UTCTime
  }

deriving stock    instance Show    Session
deriving stock    instance Generic Session
instance ToRow Session where
   toRow = genericToRow
instance FromRow Session where
   fromRow = genericFromRow


-- NB Doesn't quite correspond to the view.
data ExerciseLesson = ExerciseLesson
  { exercise         :: Key Exercise
  , lessonKey        :: Key Lesson
  , lessonName       :: Text
  , source           :: Unannotated
  , target           :: Unannotated
  , srcDir           :: Direction
  , trgDir           :: Direction
  , highlightMatches :: Bool
  , showSourceSentence :: Bool
  , exerciseOrder    :: Numeric
  }

deriving stock    instance Show    ExerciseLesson
deriving stock    instance Generic ExerciseLesson
instance ToRow ExerciseLesson where
   toRow = genericToRow
instance FromRow ExerciseLesson where
   fromRow = genericFromRow

-- NB Doesn't really correspond to the db.
data Exercise = Exercise
  { sourceLinearization :: Unannotated
  , targetLinearization :: Unannotated
  , lesson              :: Key Lesson
  , timeout             :: Numeric
  , exerciseOrder       :: Numeric
  }

deriving stock    instance Show    Exercise
deriving stock    instance Generic Exercise
instance ToRow Exercise where
   toRow = genericToRow
instance FromRow Exercise where
   fromRow = genericFromRow

data Direction = VersoRecto | RectoVerso

deriving stock    instance Show    Direction
deriving stock    instance Generic Direction
instance ToField Direction where
  toField = toField @Bool . toBool
    where
    toBool :: Direction -> Bool
    toBool = \case
      VersoRecto -> False
      RectoVerso -> True
instance FromField Direction where
  fromField = fmap fromBool <$> fromField @Bool
    where
    fromBool :: Bool -> Direction
    fromBool = \case
      False -> VersoRecto
      True -> RectoVerso

data Lesson = Lesson
  { key                 :: Key Lesson
  , name                :: Text
  , grammar             :: Text
  , sourceLanguage      :: Text
  , targetLanguage      :: Text
  , exerciseCount       :: Numeric
  , enabled             :: Bool
  , searchLimitDepth    :: Maybe Numeric
  , searchLimitSize     :: Maybe Numeric
  , repeatable          :: Bool
  , sourceDirection     :: Direction
  , targetDirection     :: Direction
  , highlightMatches    :: Bool
  , showSourceSentence  :: Bool
  , randomizeOrder      :: Bool
  }

deriving stock    instance Show    Lesson
deriving stock    instance Generic Lesson
instance ToRow Lesson where
   toRow = genericToRow
instance FromRow Lesson where
   fromRow = genericFromRow

data StartedLesson = StartedLesson
  { lesson              :: Key Lesson
  , user                :: Text
  , round               :: Numeric
  }

deriving stock    instance Show    StartedLesson
deriving stock    instance Generic StartedLesson
instance ToRow StartedLesson where
   toRow = genericToRow
instance FromRow StartedLesson where
   fromRow = genericFromRow

data FinishedLesson = FinishedLesson
  { lesson              :: Key Lesson
  , user                :: Text
  , score               :: Score
  , round               :: Numeric
  }

deriving stock    instance Show    FinishedLesson
deriving stock    instance Generic FinishedLesson
instance ToRow FinishedLesson where
   toRow = genericToRow
instance FromRow FinishedLesson where
   fromRow = genericFromRow

data ExerciseList = ExerciseList
  { user     :: Text
  , exercise :: Key Exercise
  , round    :: Numeric
  -- A 'Just' value indicates that the exercise has been solved.
  , score    :: Maybe Score
  }

deriving stock    instance Show    ExerciseList
deriving stock    instance Generic ExerciseList
instance ToRow ExerciseList where
   toRow = genericToRow
instance FromRow ExerciseList where
   fromRow = genericFromRow

-- Like below but wuthout passedcount
-- FIXME Better name
data ActiveLessonForUser = ActiveLessonForUser
  { lesson        :: Key Lesson
  , name          :: Text
  , exercisecount :: Numeric
  , score         :: Maybe Score
  , enabled       :: Bool
  , user          :: Maybe Text
  }

deriving stock    instance Show    ActiveLessonForUser
deriving stock    instance Generic ActiveLessonForUser
instance ToRow ActiveLessonForUser where
   toRow = genericToRow
instance FromRow ActiveLessonForUser where
   fromRow = genericFromRow

data UserLessonScore = UserLessonScore
  { lesson     :: Key Lesson
  , lessonName :: Text
  , user       :: Text
  , score      :: Score
  }

deriving stock    instance Show    UserLessonScore
deriving stock    instance Generic UserLessonScore
instance ToRow UserLessonScore where
   toRow = genericToRow
instance FromRow UserLessonScore where
   fromRow = genericFromRow

