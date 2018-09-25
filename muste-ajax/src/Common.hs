{-# OPTIONS_GHC -Wall #-}
{-# Language CPP #-}
module Common
  ( showPretty
  , tracePretty
  , tracePrettyId
  , traceShow
  , traceShowId
  , trace
  , throwLeft
  , decodeFileThrow
  ) where

import Prelude ()
import Muste.Prelude
import Data.Text.Prettyprint.Doc (Pretty)
import qualified Data.Text.Prettyprint.Doc as Doc
import Control.Exception (Exception, throw)
import qualified Data.Yaml as Yaml

import qualified Debug.Trace as Debug

{-# DEPRECATED traceShowId "Development aid remain in your code!!" #-}
traceShowId ∷ Show a ⇒ a → a
traceShowId = Debug.traceShowId

{-# DEPRECATED traceShow "Development aid remain in your code!!" #-}
traceShow ∷ Show a ⇒ a → b → b
traceShow = Debug.traceShow

{-# DEPRECATED trace "Development aid remain in your code!!" #-}
trace ∷ String → b → b
trace = Debug.trace

showPretty ∷ Pretty a => a → String
showPretty = show . Doc.pretty

{-# DEPRECATED tracePretty "Development aid remain in your code!!" #-}
tracePretty ∷ Pretty a ⇒ a → b → b
tracePretty a = Debug.trace (showPretty a)

{-# DEPRECATED tracePrettyId "Development aid remain in your code!!" #-}
tracePrettyId ∷ Pretty a ⇒ a → a
tracePrettyId a = Debug.trace (showPretty a) a

-- | Throws an exception if the it's a 'Left' (requires the left to be
-- an exception).  This method is *unsafe*!
throwLeft :: Exception e => Either e c -> c
throwLeft = either throw identity

decodeFileThrow ∷ MonadIO m ⇒ FromJSON a ⇒ FilePath → m a
#if MIN_VERSION_yaml(0,8,31)
decodeFileThrow = Yaml.decodeFileThrow
#else
decodeFileThrow f
  = liftIO $ Yaml.decodeFileEither f >>= either throwIO return
#endif
