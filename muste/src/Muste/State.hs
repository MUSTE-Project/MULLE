{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
{-# Language
 DeriveGeneric,
 DerivingStrategies,
 FlexibleContexts,
 GeneralizedNewtypeDeriving,
 MultiParamTypeClasses,
 OverloadedStrings,
 ScopedTypeVariables,
 StandaloneDeriving,
 TypeApplications,
 TypeFamilies,
 UndecidableInstances
#-}

module Muste.State
  ( MonadGrammar(..)
  , GrammarT
  , runGrammarT
  , getGrammar
  , getGrammarOneOff
  , HasKnownGrammars(..)
  , KnownGrammars
  , noGrammars
  , getLangAndContext
  , annotate
  ) where


import Control.Monad.Catch (MonadThrow(throwM), Exception)
import Control.Applicative (Alternative)
import Control.Monad (MonadPlus)
import Control.Monad.Base (MonadBase)
import Control.Monad.Except (ExceptT)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.Reader (MonadReader, ReaderT)
import qualified Control.Monad.Reader as Reader
import Control.Monad.Trans (MonadTrans(lift))
import Control.Monad.Trans.Control (MonadBaseControl)
import Data.IORef (IORef)
import qualified Data.IORef as IO
import Snap (MonadSnap)
import qualified Snap
import Data.Function ((&), on)

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Text (Text)

import Muste.Grammar (Grammar, readGrammar, parseSentence)
import Muste.AdjunctionTrees (BuilderInfo)
import Muste.Tree (TTree)

import Muste.Sentence
  ( Context(ctxtGrammar, ctxtLang)
  , buildContexts
  , Annotated(Annotated, language, linearization)
  , textRep
  , annotated
  , mergeL
  )


annotate :: MonadThrow m => Exception e => e -> Context -> Annotated -> m Annotated
annotate err ctxt sent
  = linearization sent
  & textRep
  & parseSentence (ctxtGrammar ctxt) (ctxtLang ctxt)
  & map unambigSimpl
  & merge err
  where
    unambigSimpl :: TTree -> Annotated
    unambigSimpl tree = annotated ctxt (language sent) tree

-- | Merge multiple
merge :: MonadThrow m => Exception e => e -> [Annotated] -> m Annotated
merge e [] = throwM e
merge _ xs = pure $ foldl1 merge1 xs

-- Merge two sentences, assuming they have the same language.
merge1 :: Annotated -> Annotated -> Annotated
merge1 a b = Annotated lang ((mergeL `on` linearization) a b)
  where
  lang = language a


-- | Given an identifier for a grammar, looks up that grammar and then
-- creates a mapping from all the languages in that grammar to their
-- respective 'Context's.
--
-- This method will throw a 'FileNotFoundException' if the grammar
-- cannot be located.
getLangAndContext :: MonadGrammar m => BuilderInfo -> Text -> m (Map Text Context)
getLangAndContext nfo idf = do
  g <- getGrammar idf
  pure $ buildContexts nfo g



newtype KnownGrammars = KnownGrammars
  -- No pun.
  { unKnownGrammars :: IORef (Map Text Grammar)
  }

noGrammars :: MonadIO io => io KnownGrammars
noGrammars = KnownGrammars <$> liftIO (IO.newIORef mempty)

-- | A monad for managing loaded grammars.
newtype GrammarT m a = GrammarT ( ReaderT KnownGrammars m a )

deriving newtype instance Functor m => Functor (GrammarT m)
deriving newtype instance Monad m => Applicative (GrammarT m)
deriving newtype instance Monad m => Monad (GrammarT m)
deriving newtype instance Monad m => MonadReader KnownGrammars (GrammarT m)
deriving newtype instance MonadIO m => MonadIO (GrammarT m)
deriving newtype instance MonadTrans GrammarT
deriving newtype instance MonadBaseControl IO m => MonadBaseControl IO (GrammarT m)
deriving newtype instance MonadBase IO m => MonadBase IO (GrammarT m)
deriving newtype instance (Alternative m, Monad m) => Alternative (GrammarT m)
deriving newtype instance (MonadSnap m) => MonadSnap (GrammarT m)
deriving newtype instance MonadPlus m => MonadPlus (GrammarT m)

class MonadIO m => MonadGrammar m where
  -- | Get the known grammars
  getKnownGrammars :: m (Map Text Grammar)
  -- | Update the known grammars with.
  insertGrammar :: Text -> Grammar -> m ()

instance MonadIO io => MonadGrammar (GrammarT io) where
  getKnownGrammars
    =   Reader.ask
    >>= liftIO . IO.readIORef . unKnownGrammars
  insertGrammar t g = do
    KnownGrammars ref  <- Reader.ask
    liftIO $ IO.modifyIORef ref $ Map.insert t g

-- Even though 'GrammarT' is implemented with a reader monad notice
-- that we pass through it here...
instance MonadGrammar m => MonadGrammar (ReaderT r m) where
  getKnownGrammars = lift getKnownGrammars
  insertGrammar t g = lift $ insertGrammar t g

instance MonadGrammar m => MonadGrammar (ExceptT r m) where
  getKnownGrammars = lift getKnownGrammars
  insertGrammar t g = lift $ insertGrammar t g

class HasKnownGrammars g where
  giveKnownGrammars :: g -> KnownGrammars

instance HasKnownGrammars w => MonadGrammar (Snap.Handler v w) where
  -- Implementation is almost identitcal to that of 'GrammarT'...
  getKnownGrammars = do
    ref <- unKnownGrammars . giveKnownGrammars <$> Reader.ask @_ @(Snap.Handler _ _)
    mp <- liftIO $ IO.readIORef ref
    liftIO $ do
      putStrLn "getKnownGrammars @Snap.Handler"
      print $ Map.size mp
    pure mp
  insertGrammar t g = do
    KnownGrammars ref  <- giveKnownGrammars <$> Reader.ask
    liftIO $ IO.modifyIORef ref $ Map.insert t g

runGrammarT :: MonadIO io => GrammarT io a -> io a
runGrammarT (GrammarT m) = do
  r <- liftIO $ IO.newIORef mempty
  Reader.runReaderT m (KnownGrammars r)

-- | Looks for a grammar at the specified location.  If the grammar is
-- found it is added to the known grammars and returned.  If the
-- grammar is not found a 'FileNotFoundException' is thrown.
getGrammar :: forall m . MonadGrammar m => Text -> m Grammar
getGrammar idf = do
  m <- getKnownGrammars
  case Map.lookup idf m of
    Nothing -> loadAndInsert idf
    Just a -> pure a

-- | A convenience method wrapping 'getGrammar' that just gets the
-- grammar once but without all the nice memoization offered by
-- 'MonadGrammar'.
getGrammarOneOff :: MonadIO io => Text -> io Grammar
getGrammarOneOff = runGrammarT . getGrammar

loadAndInsert :: forall m . MonadGrammar m => Text -> m Grammar
loadAndInsert idf = do
  g <- liftIO $ readGrammar idf
  insertGrammar idf g
  pure g
