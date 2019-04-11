{-# OPTIONS_GHC -Wall #-}
module Muste.Sentence.Token.Class (IsToken(..)) where

import Data.Text (Text)

class IsToken a where
  concrete :: a -> Text
