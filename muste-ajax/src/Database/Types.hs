{-# language
    StandaloneDeriving
  , GeneralizedNewtypeDeriving
  , TypeOperators
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
import Data.Time

import Muste (TTree)

type Blob = ByteString
type Numeric = Integer

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
