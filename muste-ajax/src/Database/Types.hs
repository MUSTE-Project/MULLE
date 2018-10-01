{-# OPTIONS_GHC -Wall #-}
{-# Language StandaloneDeriving , GeneralizedNewtypeDeriving ,
    TypeOperators , LambdaCase, DuplicateRecordFields #-}
-- | One type per table
--
-- The reason I'm using type aliases is to inherit the `FromRow` and
-- `ToRow` instances defined for these types.
module Database.Types
  ( User(..)
  , Session(..)
  , Exercise(..)
  , Lesson(..)
  , FinishedExercise(..)
  , StartedLesson(..)
  , FinishedLesson(..)
  , ExerciseList(..)
  , Muste.TTree
  , Sentence.Unannotated
  ) where

import Prelude ()
import Muste.Prelude
import Data.ByteString (ByteString)
import Data.Time

import qualified Muste (TTree)
import qualified Muste.Sentence.Unannotated as Sentence (Unannotated)
import Muste.Sentence.Unannotated (Unannotated)
import Database.SQLite.Simple.FromRow
import Database.SQLite.Simple.ToRow
import Database.SQLite.Simple.FromRow.Generic

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

deriving stock instance Show    User
deriving stock instance Generic User
instance ToRow User where
  toRow = genericToRow
instance FromRow User where
  fromRow = genericFromRow

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
instance ToRow Session where
  toRow = genericToRow
instance FromRow Session where
  fromRow = genericFromRow

-- Probably should be @(Blob, Blob, Text, Numeric)@
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
instance ToRow Exercise where
  toRow = genericToRow
instance FromRow Exercise where
  fromRow = genericFromRow

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
  , exerciseCount       ∷ Numeric
  , enabled             ∷ Bool
  , searchLimitDepth    ∷ Maybe Int
  , searchLimitSize     ∷ Maybe Int
  , repeatable          ∷ Bool
  }

deriving stock instance Show    Lesson
deriving stock instance Generic Lesson
instance ToRow Lesson where
  toRow = genericToRow
instance FromRow Lesson where
  fromRow = genericFromRow

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
  , sourceLinearization ∷ Unannotated
  , targetLinearization ∷ Unannotated
  , lesson              ∷ Text
  , time                ∷ NominalDiffTime
  , clickCount          ∷ Numeric
  , round               ∷ Numeric
  }

deriving stock instance Show    FinishedExercise
deriving stock instance Generic FinishedExercise
instance ToRow FinishedExercise where
  toRow = genericToRow
instance FromRow FinishedExercise where
  fromRow = genericFromRow

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
instance ToRow StartedLesson where
  toRow = genericToRow
instance FromRow StartedLesson where
  fromRow = genericFromRow

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
instance ToRow FinishedLesson where
  toRow = genericToRow
instance FromRow FinishedLesson where
  fromRow = genericFromRow

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
  , sourceLinearization ∷ Unannotated
  , targetLinearization ∷ Unannotated
  , lesson              ∷ Text
  , round               ∷ Numeric
  }

deriving stock instance Show    ExerciseList
deriving stock instance Generic ExerciseList
instance ToRow ExerciseList where
  toRow = genericToRow
instance FromRow ExerciseList where
  fromRow = genericFromRow
