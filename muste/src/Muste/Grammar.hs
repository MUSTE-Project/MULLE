{- | This Module gives an abstraction from the PGF format provided by GF -}
module Muste.Grammar
  ( Grammar(..)
  , Rule(..)
  , pgfToGrammar
  , isEmptyGrammar
  , getFunType
  , getAllRules
  , getRuleType
  ) where

import Muste.Grammar.Internal
