{-# OPTIONS_GHC -Wall #-}
{-# Language CPP #-}
module Muste.Web.Common
  ( module Muste.Common
  , throwLeft
  , decodeFileThrow
  ) where

import Prelude ()
import Muste.Prelude
import Muste.Common
import qualified Data.Yaml as Yaml

decodeFileThrow ∷ MonadIO m ⇒ FromJSON a ⇒ FilePath → m a
#if MIN_VERSION_yaml(0,8,31)
decodeFileThrow = Yaml.decodeFileThrow
#else
decodeFileThrow f
  = liftIO $ Yaml.decodeFileEither f >>= either throwIO return
#endif

-- | Throws an exception if the it's a 'Left' (requires the left to be
-- an exception).  This method is *unsafe*!
throwLeft :: Exception e => Either e c -> c
throwLeft = either throw identity
