{- | This Module gives an abstraction from the PGF format provided by GF -}
module Muste.Grammar (Grammar(..),pgfToGrammar,FunType(..),Rule(..),isEmptyGrammar,getAllRules,getRuleType) where

import Muste.Grammar.Internal
import Muste.Feat
