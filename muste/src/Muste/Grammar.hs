{- | This Module gives an abstraction from the PGF format provided by GF -}
module Muste.Grammar
  ( Grammar
  , Rule
  , MonadGrammar(..)
  , GrammarT
  , runGrammarT
  , getGrammar
  , HasKnownGrammars(..)
  , KnownGrammars
  , noGrammars
  ) where

import Muste.Grammar.Internal
