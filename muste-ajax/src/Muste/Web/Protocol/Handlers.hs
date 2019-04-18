-- | Defines the endpoints that the API exposes.
--
-- Module      : Muste.Web.Protocol.Handlers
-- License     : Artistic License 2.0
-- Stability   : experimental
-- Portability : POSIX
--
-- This module delegates work to "Muste.Web.Database" that handles
-- accessing the stored data as well as invoking the core logic
-- defined in package @muste@.

{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language
 DeriveAnyClass,
 FlexibleContexts,
 GADTs,
 RecordWildCards,
 ScopedTypeVariables,
 UndecidableInstances
#-}

module Muste.Web.Protocol.Handlers
  ( handleLoginRequest
  , handleLogoutRequest
  , handleLessons
  , handleLessonInit
  , handleMenuRequest
  , handleCreateUser
  , handleChangePwd
  , handleHighScores
  ) where

import Control.Category ((>>>))
import Control.Exception (throw, Exception, SomeException, ErrorCall(ErrorCall))
import Control.Monad.Catch (MonadThrow(throwM))
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Reader
import Data.Function ((&), on, id)

import Data.List.NonEmpty (NonEmpty((:|)), groupBy)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe (isJust)
import Data.Semigroup (sconcat)
import Data.Text (Text)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified GHC.Num as Math

import qualified Muste

import qualified Muste.Web.Ajax as Ajax
import qualified Muste.Web.Ajax as Lesson (Lesson(..))
import qualified Muste.Web.Ajax as ClientTree (ClientTree(..))
import qualified Muste.Web.Database as Database
import qualified Muste.Web.Database.Types as Database
import qualified Muste.Web.Database.Types as Database.UserLessonScore (UserLessonScore(..))
import qualified Muste.Web.Database.Types as ActiveLessonForUser (ActiveLessonForUser(..))
import Muste.Web.Protocol.Class
import Muste.Web.Types.Score (Score)
import qualified Muste.Web.Types.Score as Score


liftEither :: MonadError ProtocolError m => SomeException ~ e => Either e a -> m a
liftEither = either (throwError . SomeProtocolError) pure

handleCreateUser :: Ajax.CreateUser -> MULLE v ()
handleCreateUser Ajax.CreateUser{..} = 
  Database.addUser $ Database.CreateUser
    { name     = name
    , password = password
    , enabled  = True
    }

-- | Change password of the user.  The user currently (as of this
-- writing) does not need to be authenticated to change their
-- password.  They must simply provide their old password which is
-- then checked against the database.
handleChangePwd :: Ajax.ChangePassword -> MULLE v ()
handleChangePwd Ajax.ChangePassword{..} =
  Database.changePassword Database.ChangePassword
    { name = name
    , oldPassword = oldPassword
    , newPassword = newPassword
    }


handleLessons :: Ajax.LoginToken -> MULLE v Ajax.LessonList
handleLessons (Ajax.LoginToken t) = do
  Database.verifySession t
  lessons <- getActiveLessons t
  return (Ajax.LessonList lessons)


getActiveLessons :: Database.Token -> MULLE v [Ajax.ActiveLesson]
getActiveLessons t =
  fmap step . groupBy ((==) `on` ActiveLessonForUser.lesson) <$> Database.getActiveLessons t
  where
  step :: NonEmpty Database.ActiveLessonForUser -> Ajax.ActiveLesson
  step xs@(Database.ActiveLessonForUser{..} :| _) = Ajax.ActiveLesson
    { lesson        = lesson
    , name          = name
    , exercisecount = exercisecount
    , score         = sconcat <$> maybeScores
    -- This shuold be the same as asking whether 'score' is a 'Just'
    -- cell.
    , finished      = passedcount == exercisecount
    , enabled       = enabled
    , passedcount   = passedcount
    }
    where
    passedcount
      = fromIntegral
      $ length
      $ NonEmpty.filter isFinished xs
    isFinished :: Database.ActiveLessonForUser -> Bool
    isFinished = isJust . ActiveLessonForUser.score
    scores :: NonEmpty (Maybe Score)
    scores = ActiveLessonForUser.score <$> xs
    -- If just a single score is a Nothing we say that the score is a
    -- nothing.  Though they should all agree.
    maybeScores :: Maybe (NonEmpty Score)
    maybeScores = traverse id scores


handleLoginRequest :: Ajax.LoginRequest -> MULLE v Ajax.LoginToken
handleLoginRequest Ajax.LoginRequest{..} = do
  Database.authUser name password
  token <- Database.startSession name
  pure $ Ajax.LoginToken token

askContexts :: MULLE v Contexts
askContexts = asks contexts

handleLessonInit :: Ajax.StartLesson -> MULLE v Ajax.MenuResponse
handleLessonInit (Ajax.StartLesson token lesson restart) = do
  when restart $ Database.resetLesson token lesson
  Database.ExerciseLesson{..} <- Database.startLesson token lesson
  menu <- assembleMenus $ AssembleMenu
    { lesson = lessonName
    , source = Ajax.ClientTree
      { sentence = source
      , direction = dir srcDir
      }
    , target = Ajax.ClientTree
      { sentence = target
      , direction = dir trgDir
      }
    }
  return $ Ajax.MenuResponse
    { lesson = Ajax.Lesson
      { key  = lesson
      , name = lessonName
      }
    , score    = mempty
    , menu     = menu
    , lessonFinished = False
    -- Strictly speaking we can't know this for sure, but we'll just
    -- have a guess.
    , exerciseFinished = False
    , settings = Just $ Ajax.MenuSettings
      { highlightMatches = highlightMatches
      , showSourceSentence = showSourceSentence
      }
    }

dir :: Database.Direction -> Ajax.Direction
dir Database.VersoRecto = Ajax.VersoRecto
dir Database.RectoVerso = Ajax.RectoVerso

-- | This request is called after the user selects a new sentence from
-- the drop-down menu.  A request consists of two 'Ajax.ClientTree's
-- (the source and the target sentece) these can represent multiple
-- actual sentences ('TTree's).  We determine if the current exercise
-- is over by checking the source and target tree for equality.
-- 'Ajax.ClientTree's are considered equal in this case if they have
-- just one 'TTree' in common.  We respond to the caller whether the
-- exercise is over.  In either case we also return two new
-- 'Ajax.ClientTree's. For more information about what these contain
-- see the documentation there.
handleMenuRequest :: Ajax.MenuRequest -> MULLE v Ajax.MenuResponse
handleMenuRequest Ajax.MenuRequest{..} = do
  let Ajax.Score{..}  = score
      Ajax.Lesson{..} = lesson
      lessonName = Lesson.name lesson
  Database.verifySession token
  let
    newScore
      = score
      & Score.addClick 1
      & Score.setTime time
  exerciseFinished <- oneSimiliarTree lessonName src trg
  lessonFinished   <- if exerciseFinished
    then Database.finishExercise token key newScore
    else pure False
  menu <- assembleMenus $ AssembleMenu
    { lesson = lessonName
    , source = src
    , target = trg
    }
  return $ Ajax.MenuResponse
    { lesson           = lesson
    , score            = newScore
    , menu             = menu
    , lessonFinished   = lessonFinished
    , exerciseFinished = exerciseFinished
    , settings         = settings
    }

annotate :: Text -> Muste.Annotated -> MULLE v Muste.Annotated
annotate lesson sent = do
  cs <- askContexts
  liftEither $ do
    ctxt <- getContext cs lesson $ Muste.language sent
    Muste.annotate
      (ErrorCall $ "Unable to parse: " <> show sent) ctxt sent

oneSimiliarTree :: Text -> Ajax.ClientTree -> Ajax.ClientTree -> MULLE v Bool
oneSimiliarTree lesson src trg
  = do srcS <- parse src
       trgS <- parse trg
       pure $ oneInCommon srcS trgS
  where
    oneInCommon a b = not $ Set.null $ Set.intersection a b
    parse sent = fmap Set.fromList $ disambiguate lesson sent

disambiguate :: Text -> Ajax.ClientTree -> MULLE v [Muste.TTree]
disambiguate lesson Ajax.ClientTree{..} = do
  cs <- askContexts
  ctxt <- liftEither $ getContext cs lesson (Muste.language sentence)
  pure $ Muste.disambiguate ctxt sentence

handleLogoutRequest :: Ajax.LoginToken -> MULLE v ()
handleLogoutRequest (Ajax.LoginToken token) = Database.endSession token

data AssembleMenu = AssembleMenu
  { lesson :: Text
  , source :: Ajax.ClientTree
  , target :: Ajax.ClientTree
  }

-- | Gets the menus for a lesson.  This consists of a source tree and
-- a target tree.
assembleMenus :: AssembleMenu -> MULLE v Ajax.MenuList
assembleMenus AssembleMenu{..} = do
  c <- askContexts
  let mkTree = makeTree c lesson
  let ann = annotate lesson
  src <- ann $ ClientTree.sentence source
  trg <- ann $ ClientTree.sentence target
  pure $ Ajax.MenuList
    { src = mkTree src $ ClientTree.direction source
    , trg = mkTree trg $ ClientTree.direction target
    }

getContext :: MonadThrow m => Contexts -> Text -> Muste.Language -> m Muste.Context
getContext ctxts lesson lang
  =   pure ctxts
  >>= lookupM (LessonNotFound lesson) lesson
  >>= lookupM (LanguageNotFound lang) lang

lookupM :: MonadThrow m => Exception e => Ord k => e -> k -> Map k a -> m a
lookupM err k = liftMaybe err . Map.lookup k

-- | Lift a 'Maybe' to any 'MonadThrow'.
liftMaybe :: MonadThrow m => Exception e => e -> Maybe a -> m a
liftMaybe err Nothing = throwM err
liftMaybe _  (Just a) = pure a

-- | @'makeTree' ctxt lesson src trg tree@ Creates a 'ServerTree' from
-- a source trees and a target tree.  The 'Menu' is provided given
-- @tree@.
makeTree :: Contexts -> Text -> Muste.Annotated -> Ajax.Direction -> Ajax.ServerTree
makeTree c lesson s d
  = Ajax.ServerTree
  { sentence  = s
  , menu      = Muste.getMenu Muste.emptyPruneOpts ctxt (Muste.linearization s)
  , direction = d
  }
  where
  ctxt = either throw id $ getContext c lesson language
  language = Muste.language s


handleHighScores :: Ajax.LoginToken -> MULLE v [Ajax.HighScore]
handleHighScores (Ajax.LoginToken token) = do
  Database.verifySession token
  scores <- Database.getUserLessonScores
  return (step scores)

  where
  -- Group by lesson, then sort by the valuation of the score.
  step :: [Database.UserLessonScore] -> [Ajax.HighScore]
  step = NonEmpty.groupBy theLesson >>> fmap byValuation
  byValuation  = NonEmpty.sortBy theValuation >>> NonEmpty.head >>> go
  theLesson    = ((==) `on` Database.UserLessonScore.lesson)
  theValuation = compare `on` Math.negate . Score.valuation . Database.UserLessonScore.score
  go :: Database.UserLessonScore -> Ajax.HighScore
  go Database.UserLessonScore{..} = Ajax.HighScore
    { lesson = Ajax.Lesson
        { key  = lesson
        , name = lessonName
        }
    , user = Ajax.User
        { name = user
        }
    , score = score
    }

