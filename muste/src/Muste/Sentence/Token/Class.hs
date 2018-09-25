{-# OPTIONS_GHC -Wall #-}
module Muste.Sentence.Token.Class (IsToken(..)) where

-- FIXME Switch to 'Text'!
class IsToken a where
  concrete ∷ a → String
