{-# OPTIONS_GHC -Wall #-}
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
  , Muste.TTree
  , Sentence.Annotated
  ) where

import Data.ByteString (ByteString)
import Data.Text (Text)

import Data.Time

import qualified Muste (TTree)
import qualified Muste.Sentence.Annotated as Sentence (Annotated)
import Muste.Sentence.Annotated (Annotated)

type Blob = ByteString
type Numeric = Integer

-- | Representation of a 'User' in the database.  Consists of:
--
-- * User name.
-- * Password.
-- * Salt.
-- * Is user enabled.
type User =
  ( Text            -- @username@
  , Blob            -- @password@
  , Blob            -- @salt@
  , Bool            -- @enabled@
  )

-- | Representation of a 'Session' in the database.  Consists of:
--
-- * User name.
-- * A token.
-- * Start time.
-- * End time.
type Session =
  ( Text            -- @user@
  , Text            -- @token@
  , UTCTime         -- @starttime@
  , UTCTime         -- @lastActive@
  )

-- Probably should be @(Blob, Blob, Text, Numeric)@
-- | Representation of an 'Exercise' in the database.  Consists of:
--
-- * The source sentence.
-- * The target sentence.
-- * The lesson to which the exercise belongs.
-- * Timeout for the exercise.
type Exercise =
  ( Annotated -- @sourceTree@
  , Annotated -- @targetTree@
  , Text      -- @lesson@
  , Numeric   -- @timeout@
  )

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
type Lesson =
  ( Text            -- @name@
  , Text            -- @description@
  , Text            -- @grammar@
  , Text            -- @sourceLanguage@
  , Text            -- @targetLanguage@
  , Numeric         -- @exerciseCount@
  , Bool            -- @enabled@
  , Bool            -- @repeatable@
  )

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
type FinishedExercise =
  ( Text            -- @user@
  , Annotated       -- @sourceTree@
  , Annotated       -- @targetTree@
  , Text            -- @lesson@
  , NominalDiffTime -- @time@
  , Numeric         -- @clickCount@
  , Numeric         -- @round@
  )

-- | Representation of a 'StartedLesson' in the
-- database.  Consists of:
--
-- * The name of the lesson.
-- * The (name of the) user that started the lessson.
-- * The round.
type StartedLesson =
  ( Text            -- @lesson@
  , Text            -- @user@
  , Numeric         -- @round@
  )

-- | Representation of a 'FinishedLesson' in the
-- database.  Consists of:
--
-- * The name of the lesson.
-- * The (name of the) user that finished the exercise.
-- * The time it took to finish the exercise.
-- * The number of clicks it took to finish.
-- * The number of rounds.
type FinishedLesson =
  ( Text            -- @lesson@
  , Text            -- @user@
  , Numeric         -- @time@
  , Numeric         -- @clickCount@
  , Numeric         -- @round@
  )

-- | Representation of an 'ExerciseList' in the database.  Consists
-- of:
--
-- * User name.
-- * Source language.
-- * Target language.
-- * The lesson it belongs to.
-- * The round.
type ExerciseList =
  ( Text      -- @user@
  , Annotated -- @sourceTree@
  , Annotated -- @targetTree@
  , Text      -- @lesson@
  , Numeric   -- @round@
  )
