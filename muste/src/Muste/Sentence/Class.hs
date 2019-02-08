{-# OPTIONS_GHC -Wall #-}
{-# Language ConstraintKinds #-}

module Muste.Sentence.Class
  ( Sentence(..)
  , module Muste.Sentence.Language
  , module Muste.Sentence.Linearization
  ) where

import Muste.Sentence.Language
import Muste.Sentence.Linearization

class Sentence a where
  type Token a
  language :: a -> Language
  linearization :: a -> Linearization (Token a)
  sentence :: Language -> Linearization (Token a) -> a
