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
import Data.Text (Text)
import qualified Data.Text as Text

import Muste.Grammar
import Muste.Linearization
import Muste.Common
import qualified Muste.Linearization.Internal as Linearization

unsafeGetContext ∷ BuilderInfo → Grammar → Text → Context
unsafeGetContext nfo g lang = fromMaybe err $ getCtxt nfo g lang
  where
  err = error $ printf cantFindLang $ Text.unpack lang

getCtxt ∷ MonadFail m ⇒ BuilderInfo → Grammar → Text → m Context
getCtxt nfo g lang = lookupFail err lang $ Linearization.readLangs nfo g
  where
  err = printf cantFindLang $ Text.unpack lang

cantFindLang ∷ String
cantFindLang = "Cannot find language: \"%s\""
