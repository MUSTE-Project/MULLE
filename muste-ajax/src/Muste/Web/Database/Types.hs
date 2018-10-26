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
import Muste.Prelude.SQL
  ( FromRow
  , ToRow
  , ToField(..)
  , FromField(..)
  , ToNamed(..)
  , NamedParam(..)
  )
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
instance ToNamed User where
  toNamed User{..} =
    [ ":Id"        := key
    , ":Username"  := name
    , ":Password"  := password
    , ":Salt"      := salt
    , ":Enabled"   := enabled
    ]

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
instance ToNamed UserSansId where
  toNamed UserSansId{..} =
    [ ":Username"  := name
    , ":Password"  := password
    , ":Salt"      := salt
    , ":Enabled"   := enabled
    ]

data CreateUser = CreateUser
  { name     ∷ Text
  , password ∷ Text
  , enabled  ∷ Bool
  }

deriving stock    instance Show    CreateUser
deriving stock    instance Generic CreateUser
deriving anyclass instance ToRow   CreateUser
deriving anyclass instance FromRow CreateUser
instance ToNamed CreateUser where
  toNamed CreateUser{..} =
    [ ":Username"  := name
    , ":Password"  := password
    , ":Enabled"   := enabled
    ]

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
instance ToNamed ChangePassword where
  toNamed ChangePassword{..} =
    [ ":Username"    := name
    , ":OldPassword" := oldPassword
    , ":NewPassword" := newPassword
    ]

newtype Token = Token Text

deriving stock    instance Show      Token
deriving stock    instance Generic   Token
deriving newtype  instance ToField   Token
deriving newtype  instance FromField Token

-- NB Missing the key to be exactly the same as the stuff in the db.
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
instance ToNamed Session where
  toNamed Session{..} =
    [ ":User"        := user
    , ":Token"       := token
    , ":Starttime"   := startTime
    , ":LastActive"  := lastActive
    ]

-- NB Doesn't quite correspond to the view.
data ExerciseLesson = ExerciseLesson
  { exercise         ∷ Key Exercise
  , lessonKey        ∷ Key Lesson
  , lessonName       ∷ Text
  , source           ∷ Unannotated
  , target           ∷ Unannotated
  , srcDir           ∷ Direction
  , trgDir           ∷ Direction
  , highlightMatches ∷ Bool
  , exerciseOrder    ∷ Numeric
  }

deriving stock    instance Show    ExerciseLesson
deriving stock    instance Generic ExerciseLesson
deriving anyclass instance ToRow   ExerciseLesson
deriving anyclass instance FromRow ExerciseLesson
instance ToNamed ExerciseLesson where
  toNamed ExerciseLesson{..} =
    [ ":Exercise"         := exercise
    , ":LessonKey"        := lessonKey
    , ":LessonName"       := lessonName
    , ":Source"           := source
    , ":Target"           := target
    , ":SrcDir"           := srcDir
    , ":TrgDir"           := trgDir
    , ":HighlightMatches" := highlightMatches
    , ":ExerciseOrder"    := exerciseOrder
    ]

-- NB Doesn't really correspond to the db.
data Exercise = Exercise
  { sourceLinearization ∷ Unannotated
  , targetLinearization ∷ Unannotated
  , lesson              ∷ Key Lesson
  , timeout             ∷ Numeric
  , exerciseOrder       ∷ Numeric
  }

deriving stock    instance Show    Exercise
deriving stock    instance Generic Exercise
deriving anyclass instance ToRow   Exercise
deriving anyclass instance FromRow Exercise
instance ToNamed Exercise where
  toNamed Exercise{..} =
    [ ":SourceLinearization" := sourceLinearization
    , ":TargetLinearization" := targetLinearization
    , ":Lesson"              := lesson
    , ":Timeout"             := timeout
    , ":ExerciseOrder"       := exerciseOrder
    ]

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
  , exerciseCount       ∷ Numeric
  , enabled             ∷ Bool
  , searchLimitDepth    ∷ Maybe Numeric
  , searchLimitSize     ∷ Maybe Numeric
  , repeatable          ∷ Bool
  , sourceDirection     ∷ Direction
  , targetDirection     ∷ Direction
  , highlightMatches    ∷ Bool
  , randomizeOrder      ∷ Bool
  }

deriving stock    instance Show    Lesson
deriving stock    instance Generic Lesson
deriving anyclass instance ToRow   Lesson
deriving anyclass instance FromRow Lesson
instance ToNamed Lesson where
  toNamed Lesson{..} =
    [ ":Id"                := key
    , ":Name"              := name
    , ":Description"       := description
    , ":Grammar"           := grammar
    , ":SourceLanguage"    := sourceLanguage
    , ":TargetLanguage"    := targetLanguage
    , ":ExerciseCount"     := exerciseCount
    , ":Enabled"           := enabled
    , ":SearchLimitDepth"  := searchLimitDepth
    , ":SearchLimitSize"   := searchLimitSize
    , ":Repeatable"        := repeatable
    , ":SourceDirection"   := sourceDirection
    , ":TargetDirection"   := targetDirection
    , ":HighlightMatches"  := highlightMatches
    , ":RandomizeOrder"    := randomizeOrder
    ]

data StartedLesson = StartedLesson
  { lesson              ∷ Key Lesson
  , user                ∷ Key User
  , round               ∷ Numeric
  }

deriving stock    instance Show    StartedLesson
deriving stock    instance Generic StartedLesson
deriving anyclass instance ToRow   StartedLesson
deriving anyclass instance FromRow StartedLesson
instance ToNamed StartedLesson where
  toNamed StartedLesson{..} =
    [ ":Lesson"   := lesson
    , ":User"     := user
    , ":Round"    := round
    ]

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
instance ToNamed FinishedLesson where
  toNamed FinishedLesson{..} =
    [ ":Lesson" := lesson
    , ":User"   := user
    , ":Score"  := score
    , ":Round"  := score
    ]

data ExerciseList = ExerciseList
  { user     ∷ Key User
  , exercise ∷ Key Exercise
  , round    ∷ Numeric
  -- A 'Just' value indicates that the exercise has been solved.
  , score    ∷ Maybe Score
  }

deriving stock    instance Show    ExerciseList
deriving stock    instance Generic ExerciseList
deriving anyclass instance ToRow   ExerciseList
deriving anyclass instance FromRow ExerciseList
instance ToNamed ExerciseList where
  toNamed ExerciseList{..} =
    [ ":User"      := user
    , ":Exercise"  := exercise
    , ":Round"     := round
    , ":Score"     := score
    ]

-- Like below but wuthout passedcount
-- FIXME Better name
data ActiveLessonForUser = ActiveLessonForUser
  { lesson        ∷ Key Lesson
  , name          ∷ Text
  , description   ∷ Text
  , exercisecount ∷ Numeric
  , score         ∷ Maybe Score
  , enabled       ∷ Bool
  , user          ∷ Maybe (Key User)
  }

deriving stock    instance Show    ActiveLessonForUser
deriving stock    instance Generic ActiveLessonForUser
deriving anyclass instance ToRow   ActiveLessonForUser
deriving anyclass instance FromRow ActiveLessonForUser
instance ToNamed ActiveLessonForUser where
  toNamed ActiveLessonForUser{..} =
    [ ":Lesson"        := lesson
    , ":Name"          := name
    , ":Description"   := description
    , ":Exercisecount" := exercisecount
    , ":Score"         := score
    , ":Enabled"       := enabled
    , ":User"          := user
    ]

-- FIXME Just belongs in "Muste.Web.Ajax".
-- | Not like 'Types.Lesson'.  'Types.Lesson' refers to the
-- representation in the database.  This is the type used in "Ajax".
data ActiveLesson = ActiveLesson
  { lesson        ∷ Key Lesson
  , name          ∷ Text
  , description   ∷ Text
  , exercisecount ∷ Numeric
  , passedcount   ∷ Numeric
  , score         ∷ Maybe Score
  , finished      ∷ Bool
  , enabled       ∷ Bool
  }

deriving stock    instance Show    ActiveLesson
deriving stock    instance Generic ActiveLesson

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
instance ToNamed UserLessonScore where
  toNamed UserLessonScore{..} =
    [ ":Lesson"     := lesson
    , ":LessonName" := lessonName
    , ":User"       := user
    , ":UserName"   := userName
    , ":Score"      := score
    ]
