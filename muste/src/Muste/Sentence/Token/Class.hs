{-# OPTIONS_GHC -Wall #-}
module Muste.Sentence.Token.Class (IsToken(..)) where

import Prelude ()
import Muste.Prelude

class IsToken a where
  concrete :: a -> Text
