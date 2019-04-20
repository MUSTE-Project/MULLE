{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}

module Muste.State
  ( MUSTE
  , runMUSTE
  , getGrammar
  , getGrammarOneOff
  , getLangAndContext
  , annotate
  ) where


import Control.Monad.Catch (MonadThrow(throwM), Exception)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.Reader (ReaderT)
import qualified Control.Monad.Reader as Reader
import Data.IORef (IORef)
import qualified Data.IORef as IO
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



-- -- | A monad for managing loaded grammars.
type MUSTE = ReaderT (IORef KnownGrammars) IO

type KnownGrammars = Map Text Grammar

-- | Given an identifier for a grammar, looks up that grammar and then
-- creates a mapping from all the languages in that grammar to their
-- respective 'Context's.
--
-- This method will throw a 'FileNotFoundException' if the grammar
-- cannot be located.
getLangAndContext :: BuilderInfo -> Text -> MUSTE (Map Text Context)
getLangAndContext nfo idf = do
  g <- getGrammar idf
  pure $ buildContexts nfo g

getKnownGrammars :: MUSTE KnownGrammars
getKnownGrammars
  = do ref <- Reader.ask
       liftIO $ IO.readIORef ref

insertGrammar :: Text -> Grammar -> MUSTE ()
insertGrammar name grammar
  = do ref  <- Reader.ask
       liftIO $ IO.modifyIORef ref $ Map.insert name grammar

runMUSTE :: MUSTE a -> IO a
runMUSTE m
  = do ref <- liftIO $ IO.newIORef mempty
       Reader.runReaderT m ref

-- | Looks for a grammar at the specified location.  If the grammar is
-- found it is added to the known grammars and returned.  If the
-- grammar is not found a 'FileNotFoundException' is thrown.
getGrammar :: Text -> MUSTE Grammar
getGrammar idf
  = do m <- getKnownGrammars
       case Map.lookup idf m of
         Nothing -> loadAndInsert idf
         Just a -> return a

-- | A convenience method wrapping 'getGrammar' that just gets the
-- grammar once but without all the nice memoization offered by
-- 'MonadGrammar'.
getGrammarOneOff :: Text -> IO Grammar
getGrammarOneOff = runMUSTE . getGrammar

loadAndInsert :: Text -> MUSTE Grammar
loadAndInsert idf
  = do grammar <- liftIO $ readGrammar idf
       insertGrammar idf grammar
       return grammar
