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
{-# Language StandaloneDeriving , GeneralizedNewtypeDeriving ,
    TypeOperators , DuplicateRecordFields, DeriveAnyClass,
    RecordWildCards #-}

module Muste.Web.Database.Types
  ( User(..)
  , UserSansId(..)
  , CreateUser(..)
  , ChangePassword(..)
  , Session(..)
  , Exercise(..)
  , Lesson(..)
  , FinishedExercise(..)
  , StartedLesson(..)
  , FinishedLesson(..)
  , ExerciseList(..)
  , ActiveLessonForUser(..)
  , ActiveLesson(..)
  , UserLessonScore(..)
  , Key(..)
  , Muste.TTree
  , Sentence.Unannotated
  , Blob(..)
  , Numeric(..)
  , ExerciseLesson(..)
  , Direction(..)
  , Token(..)
  ) where

import Prelude ()
import Muste.Prelude
import Muste.Prelude.SQL (FromRow, ToRow, Nullable, ToField(..), FromField(..))
import Data.Int (Int64)

import Data.ByteString (ByteString)
import Data.Aeson (FromJSON(..), (.:), ToJSON(..), (.=))
import qualified Data.Aeson as Aeson

import qualified Muste (TTree)
import qualified Muste.Sentence.Unannotated as Sentence (Unannotated)
import Muste.Sentence.Unannotated (Unannotated)

import Muste.Web.Types.Score (Score)

newtype Blob = Blob { unBlob ∷ ByteString }

deriving stock   instance Show      Blob
deriving newtype instance Eq        Blob
deriving newtype instance ToField   Blob
deriving newtype instance FromField Blob

-- | The sql driver we use uses 64 bit integers meaning that we
-- anyways convert to and from this.  sqlite3s documentation has this to say:
--
-- > INTEGER. The value is a signed integer, stored in 1, 2, 3, 4, 6,
-- > or 8 bytes depending on the magnitude of the value.
newtype Numeric = Numeric { unNumeric ∷ Int64 }

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
data Key a = Key { unKey ∷ Int64 }

deriving stock instance Show      (Key a)
instance ToField   (Key a) where
  toField = toField . unKey
instance FromField (Key a) where
  fromField = fmap Key . fromField
instance ToJSON    (Key a) where
  toJSON = toJSON . unKey
instance FromJSON  (Key a) where
  parseJSON = fmap Key . parseJSON

data User = User
  { key                 ∷ Key User
  , name                ∷ Text
  , password            ∷ Blob
  , salt                ∷ Blob
  , enabled             ∷ Bool
  }

deriving stock    instance Show    User
deriving stock    instance Generic User
deriving anyclass instance ToRow   User
deriving anyclass instance FromRow User

data UserSansId = UserSansId
  { name                ∷ Text
  , password            ∷ Blob
  , salt                ∷ Blob
  , enabled             ∷ Bool
  }

deriving stock    instance Show    UserSansId
deriving stock    instance Generic UserSansId
deriving anyclass instance ToRow   UserSansId
deriving anyclass instance FromRow UserSansId

data CreateUser = CreateUser
  { name     ∷ Text
  , password ∷ Text
  , enabled  ∷ Bool
  }

deriving stock    instance Show    CreateUser
deriving stock    instance Generic CreateUser
deriving anyclass instance ToRow   CreateUser
deriving anyclass instance FromRow CreateUser

-- If we made it so that only /already/ authenticated users could
-- change their password, then we ought to change to a user id here in
-- stead of their name.
data ChangePassword = ChangePassword
  { name        ∷ Text
  , oldPassword ∷ Text
  , newPassword ∷ Text
  }

deriving stock    instance Show    ChangePassword
deriving stock    instance Generic ChangePassword
deriving anyclass instance ToRow   ChangePassword
deriving anyclass instance FromRow ChangePassword

newtype Token = Token Text

deriving stock    instance Show      Token
deriving stock    instance Generic   Token
deriving newtype  instance ToField   Token
deriving newtype  instance FromField Token

-- | Representation of a 'Session' in the database.  Consists of:
--
-- * User name.
-- * A token.
-- * Start time.
-- * End time.
data Session = Session
  { user                ∷ Key User
  , token               ∷ Token
  , startTime           ∷ UTCTime
  , lastActive          ∷ UTCTime
  }

deriving stock    instance Show    Session
deriving stock    instance Generic Session
deriving anyclass instance ToRow   Session
deriving anyclass instance FromRow Session

data ExerciseLesson = ExerciseLesson
  { exercise         ∷ Key Exercise
  , lessonKey        ∷ Key Lesson
  , lessonName       ∷ Text
  , source           ∷ Unannotated
  , target           ∷ Unannotated
  , srcDir           ∷ Direction
  , trgDir           ∷ Direction
  , highlightMatches ∷ Bool
  }

deriving stock    instance Show    ExerciseLesson
deriving stock    instance Generic ExerciseLesson
deriving anyclass instance ToRow   ExerciseLesson
deriving anyclass instance FromRow ExerciseLesson

-- | Representation of an 'Exercise' in the database.  Consists of:
--
-- * The source sentence.
-- * The target sentence.
-- * The lesson to which the exercise belongs.
-- * Timeout for the exercise.
data Exercise = Exercise
  { sourceLinearization ∷ Unannotated
  , targetLinearization ∷ Unannotated
  , lesson              ∷ Key Lesson
  , timeout             ∷ Numeric
  }

deriving stock    instance Show    Exercise
deriving stock    instance Generic Exercise
deriving anyclass instance ToRow   Exercise
deriving anyclass instance FromRow Exercise

data Direction = VersoRecto | RectoVerso

deriving stock    instance Show    Direction
deriving stock    instance Generic Direction
instance ToField Direction where
  toField = toField @Bool . toBool
    where
    toBool ∷ Direction → Bool
    toBool = \case
      VersoRecto → False
      RectoVerso → True
instance FromField Direction where
  fromField = fmap fromBool <$> fromField @Bool
    where
    fromBool ∷ Bool → Direction
    fromBool = \case
      False → VersoRecto
      True → RectoVerso

data Lesson = Lesson
  { key                 ∷ Key Lesson
  , name                ∷ Text
  , description         ∷ Text
  , grammar             ∷ Text
  , sourceLanguage      ∷ Text
  , targetLanguage      ∷ Text
  -- TODO Why not let the dbms manage this?
  , exerciseCount       ∷ Numeric
  , enabled             ∷ Bool
  , searchLimitDepth    ∷ Maybe Numeric
  , searchLimitSize     ∷ Maybe Numeric
  , repeatable          ∷ Bool
  , sourceDirection     ∷ Direction
  , targetDirection     ∷ Direction
  , highlightMatches    ∷ Bool
  }

deriving stock    instance Show    Lesson
deriving stock    instance Generic Lesson
deriving anyclass instance ToRow   Lesson
deriving anyclass instance FromRow Lesson

-- | Representation of a 'FinishedExercise' in the database.  Consists
-- of:
--
-- * The username of the one who finished it.
-- * The source sentence.
-- * The target sentence.
-- * The name of the lesson it belongs to.
-- * The time it took to finish.
-- * The amount of clicks it took.
-- * The round it was in the lesson.
data FinishedExercise = FinishedExercise
  { user                ∷ Key User
  , exercise            ∷ Key Exercise
  , score               ∷ Score
  , round               ∷ Numeric
  }

deriving stock    instance Show    FinishedExercise
deriving stock    instance Generic FinishedExercise
deriving anyclass instance ToRow   FinishedExercise
deriving anyclass instance FromRow FinishedExercise

-- | Representation of a 'StartedLesson' in the
-- database.  Consists of:
--
-- * The name of the lesson.
-- * The (name of the) user that started the lessson.
-- * The round.
data StartedLesson = StartedLesson
  { lesson              ∷ Key Lesson
  , user                ∷ Key User
  , round               ∷ Numeric
  }

deriving stock    instance Show    StartedLesson
deriving stock    instance Generic StartedLesson
deriving anyclass instance ToRow   StartedLesson
deriving anyclass instance FromRow StartedLesson

-- | Representation of a 'FinishedLesson' in the
-- database.  Consists of:
--
-- * The name of the lesson.
-- * The (name of the) user that finished the exercise.
-- * The time it took to finish the exercise.
-- * The number of clicks it took to finish.
-- * The number of rounds.
data FinishedLesson = FinishedLesson
  { lesson              ∷ Key Lesson
  , user                ∷ Key User
  , score               ∷ Score
  , round               ∷ Numeric
  }

deriving stock    instance Show    FinishedLesson
deriving stock    instance Generic FinishedLesson
deriving anyclass instance ToRow   FinishedLesson
deriving anyclass instance FromRow FinishedLesson

-- | Representation of an 'ExerciseList' in the database.  Consists
-- of:
--
-- * User name.
-- * Source language.
-- * Target language.
-- * The lesson it belongs to.
-- * The round.
data ExerciseList = ExerciseList
  { user     ∷ Key User
  , exercise ∷ Key Exercise
  , round    ∷ Numeric
  }

deriving stock    instance Show    ExerciseList
deriving stock    instance Generic ExerciseList
deriving anyclass instance ToRow   ExerciseList
deriving anyclass instance FromRow ExerciseList

-- Like below but wuthout passedcount
-- FIXME Better name
data ActiveLessonForUser = ActiveLessonForUser
  { lesson        ∷ Key Lesson
  , name          ∷ Text
  , description   ∷ Text
  , exercisecount ∷ Numeric
  , score         ∷ Nullable Score
  , finished      ∷ Bool
  , enabled       ∷ Bool
  , user          ∷ Maybe (Key User)
  }

deriving stock    instance Show    ActiveLessonForUser
deriving stock    instance Generic ActiveLessonForUser
deriving anyclass instance ToRow   ActiveLessonForUser
deriving anyclass instance FromRow ActiveLessonForUser

-- | Not like 'Types.Lesson'.  'Types.Lesson' refers to the
-- representation in the database.  This is the type used in "Ajax".
data ActiveLesson = ActiveLesson
  { lesson        ∷ Key Lesson
  , name          ∷ Text
  , description   ∷ Text
  , exercisecount ∷ Numeric
  , passedcount   ∷ Numeric
  , score         ∷ Score
  , finished      ∷ Bool
  , enabled       ∷ Bool
  }

deriving stock    instance Show    ActiveLesson
deriving stock    instance Generic ActiveLesson
deriving anyclass instance ToRow   ActiveLesson
deriving anyclass instance FromRow ActiveLesson

instance FromJSON ActiveLesson where
  parseJSON = Aeson.withObject "Lesson"
    $ \v -> ActiveLesson
    <$> v .: "lesson"
    <*> v .: "name"
    <*> v .: "description"
    <*> v .: "exercisecount"
    <*> v .: "passedcount"
    <*> v .: "score"
    <*> v .: "passed"
    <*> v .: "enabled"

instance ToJSON ActiveLesson where
  toJSON ActiveLesson{..} = Aeson.object
    [ "lesson"        .= lesson
    , "name"          .= name
    , "description"   .= description
    , "exercisecount" .= exercisecount
    , "passedcount"   .= passedcount
    , "score"         .= score
    , "passed"        .= finished
    , "enabled"       .= enabled
    ]

data UserLessonScore = UserLessonScore
  { lesson     ∷ Key Lesson
  , lessonName ∷ Text
  , user       ∷ Key User
  , userName   ∷ Text
  , score      ∷ Score
  }

deriving stock    instance Show    UserLessonScore
deriving stock    instance Generic UserLessonScore
deriving anyclass instance ToRow   UserLessonScore
deriving anyclass instance FromRow UserLessonScore
