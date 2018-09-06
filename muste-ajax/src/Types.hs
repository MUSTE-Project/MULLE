{-# OPTIONS_GHC -Wall #-}
-- | One type per table
module Database.Types
  ( User
  , Session
  , Exercise
  , Lesson
  , FinishedExercise
  , StartedLesson
  , FinishedLesson
  , ExerciseList
  ) where

data User
instance FromRow User where

data Session
instance FromRow Session where

data Exercise
instance FromRow Exercise where

data Lesson
instance FromRow Lesson where

data FinishedExercise
instance FromRow FinishedExercise where

data StartedLesson
instance FromRow StartedLesson where

data FinishedLesson
instance FromRow FinishedLesson where

data ExerciseList
instance FromRow ExerciseList where

