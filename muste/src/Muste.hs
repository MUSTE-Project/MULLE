{-# OPTIONS_GHC -Wall -Wcompat #-}
-- | High level API to the muste backend.
module Muste
  ( -- * Trees
    module Muste.Tree
  -- * Grammar
  , module Muste.Grammar
  -- * Menus
  , module Muste.Menu
  -- * Linearization
  , module Muste.Linearization
  ) where

import Muste.Tree
import Muste.Grammar
import Muste.Menu          hiding (PruneOpts(..))
import Muste.Linearization hiding (BuilderInfo(..))
