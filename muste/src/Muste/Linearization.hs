module Muste.Linearization
  ( Linearization
  , Context(ctxtGrammar, ctxtPrecomputed)
  , buildContext
  , getLangAndContext
  , mkLin
  , disambiguate
  , BuilderInfo(..)
  ) where

import Muste.Linearization.Internal
