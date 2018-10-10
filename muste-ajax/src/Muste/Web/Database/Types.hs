{-# OPTIONS_GHC -Wall #-}
{-# Language StandaloneDeriving , GeneralizedNewtypeDeriving ,
    TypeOperators , DuplicateRecordFields, DeriveAnyClass, RecordWildCards #-}
-- | One type per table
--
-- The reason I'm using type aliases is to inherit the `FromRow` and
-- `ToRow` instances defined for these types.
module Muste.Web.Database.Types
  ( User(..)
  , Session(..)
  , Exercise(..)
  , Lesson(..)
  , FinishedExercise(..)
  , StartedLesson(..)
  , FinishedLesson(..)
  , ExerciseList(..)
  , ActiveLesson(..)
  , Muste.TTree
  , Sentence.Unannotated
  , Numeric
  , Blob
  ) where

import Prelude ()
import Muste.Prelude
import Data.ByteString (ByteString)
import Data.Time
import Data.Aeson (FromJSON(..), (.:), ToJSON(..), (.=))
import qualified Data.Aeson as Aeson

import qualified Muste (TTree)
import qualified Muste.Sentence.Unannotated as Sentence (Unannotated)
import Muste.Sentence.Unannotated (Unannotated)
import Database.SQLite.Simple.FromRow
import Database.SQLite.Simple.ToRow

import           Muste.Web.Types.Score (Score)

type Blob = ByteString
type Numeric = Integer

-- | Representation of a 'User' in the database.  Consists of:
--
-- * User name.
-- * Password.
-- * Salt.
-- * Is user enabled.
data User = User
  { userName            ∷ Text
  , password            ∷ Blob
  , salt                ∷ Blob
  , enabled             ∷ Bool
  }

deriving stock    instance Show    User
deriving stock    instance Generic User
deriving anyclass instance ToRow User
deriving anyclass instance FromRow User

-- | Representation of a 'Session' in the database.  Consists of:
--
-- * User name.
-- * A token.
-- * Start time.
-- * End time.
data Session = Session
  { user                ∷ Text
  , token               ∷ Text
  , startTime           ∷ UTCTime
  , lastActive          ∷ UTCTime
  }

deriving stock instance Show    Session
deriving stock instance Generic Session
deriving anyclass instance ToRow Session
deriving anyclass instance FromRow Session

-- | Representation of an 'Exercise' in the database.  Consists of:
--
-- * The source sentence.
-- * The target sentence.
-- * The lesson to which the exercise belongs.
-- * Timeout for the exercise.
data Exercise = Exercise
  { sourceLinearization ∷ Unannotated
  , targetLinearization ∷ Unannotated
  , lesson              ∷ Text
  , timeout             ∷ Numeric
  }

deriving stock instance Show    Exercise
deriving stock instance Generic Exercise
deriving anyclass instance ToRow Exercise
deriving anyclass instance FromRow Exercise

-- | Representation of a 'Leson' in the database.  Consists of:
--
-- * A name.
-- * A description.
-- * The grammar for the exercise.  This is a path to where the
--   '.pgf'-file is stored.
-- * The source language.
-- * The target language.
-- * The number of exercises.
-- * Is it enabled.
-- * Is it repeatable.
data Lesson = Lesson
  { name                ∷ Text
  , description         ∷ Text
  , grammar             ∷ Text
  , sourceLanguage      ∷ Text
  , targetLanguage      ∷ Text
  -- TODO Why not let the dbms manage this?
  , exerciseCount       ∷ Numeric
  , enabled             ∷ Bool
  , searchLimitDepth    ∷ Maybe Int
  , searchLimitSize     ∷ Maybe Int
  , repeatable          ∷ Bool
  }

deriving stock instance Show    Lesson
deriving stock instance Generic Lesson
deriving anyclass instance ToRow Lesson
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
  { user                ∷ Text
  , lesson              ∷ Text
  , sourceSentence      ∷ Unannotated
  , targetSentence      ∷ Unannotated
  , score               ∷ Score
  , round               ∷ Numeric
  }

deriving stock instance Show    FinishedExercise
deriving stock instance Generic FinishedExercise
deriving anyclass instance ToRow FinishedExercise
deriving anyclass instance FromRow FinishedExercise

-- | Representation of a 'StartedLesson' in the
-- database.  Consists of:
--
-- * The name of the lesson.
-- * The (name of the) user that started the lessson.
-- * The round.
data StartedLesson = StartedLesson
  { lesson              ∷ Text
  , user                ∷ Text
  , round               ∷ Numeric
  }

deriving stock instance Show    StartedLesson
deriving stock instance Generic StartedLesson
deriving anyclass instance ToRow StartedLesson
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
  { lesson              ∷ Text
  , user                ∷ Text
  , time                ∷ Numeric
  , clickCount          ∷ Numeric
  , round               ∷ Numeric
  }

deriving stock instance Show    FinishedLesson
deriving stock instance Generic FinishedLesson
deriving anyclass instance ToRow FinishedLesson
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
  { user                ∷ Text
  , lesson              ∷ Text
  , sourceSentence      ∷ Unannotated
  , targetSentence      ∷ Unannotated
  , round               ∷ Numeric
  }

deriving stock instance Show    ExerciseList
deriving stock instance Generic ExerciseList
deriving anyclass instance ToRow ExerciseList
deriving anyclass instance FromRow ExerciseList


-- | Not like 'Types.Lesson'.  'Types.Lesson' refers to the
-- representation in the database.  This is the type used in "Ajax".
data ActiveLesson = ActiveLesson
  { name          ∷ Text
  , description   ∷ Text
  , exercisecount ∷ Int
  , passedcount   ∷ Int
  , score         ∷ Maybe Score
  , finished      ∷ Bool
  , enabled       ∷ Bool
  }

deriving stock instance Show ActiveLesson

instance FromJSON ActiveLesson where
  parseJSON = Aeson.withObject "Lesson"
    $ \v -> ActiveLesson
    <$> v .: "name"
    <*> v .: "description"
    <*> v .: "exercisecount"
    <*> v .: "passedcount"
    <*> v .: "score"
    <*> v .: "passed"
    <*> v .: "enabled"

instance ToJSON ActiveLesson where
  toJSON ActiveLesson{..} = Aeson.object
    [ "name"          .= name
    , "description"   .= description
    , "exercisecount" .= exercisecount
    , "passedcount"   .= passedcount
    , "score"         .= score
    , "passed"        .= finished
    , "enabled"       .= enabled
    ]

deriving stock instance Generic ActiveLesson
deriving anyclass instance ToRow ActiveLesson
deriving anyclass instance FromRow ActiveLesson
