-- | Helper functions just like in 'Muste.Common', but these helpers
-- build *on top* of functionality from `muste` (to be used in the CLI
-- and the tests)
module Muste.Util
  ( unsafeGetContext
  , getCtxt
  ) where

import Control.Monad.Fail (MonadFail(fail))
import Text.Printf
import Data.Maybe

import Muste
import Muste.Common
import qualified Muste.Linearization.Internal as Linearization

unsafeGetContext ∷ Grammar → String → Context
unsafeGetContext g lang = fromMaybe err $ getCtxt g lang
  where
  err = error $ printf "Can't find %s" lang

getCtxt ∷ MonadFail m ⇒ Grammar → String → m Context
getCtxt g lang = lookupFail err lang $ Linearization.readLangs g
  where
  err = printf "Can't find %s" lang


