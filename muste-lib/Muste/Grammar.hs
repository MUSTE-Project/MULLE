{- | This Module gives an abstraction from the PGF format provided by GF -}
module Muste.Grammar (Grammar(..),FunType(..),wildCard,pgfToGrammar,isEmptyGrammar,getFunType) where

import Muste.Grammar.Internal
import Muste.Feat
