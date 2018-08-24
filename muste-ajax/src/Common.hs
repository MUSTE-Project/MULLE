module Common (prettyShow, prettyTrace, prettyTraceId) where

import Data.Text.Prettyprint.Doc (Pretty)
import qualified Data.Text.Prettyprint.Doc as Doc

import Debug.Trace

prettyShow ∷ Pretty a => a → String
prettyShow = show . Doc.pretty

{-# DEPRECATED prettyTrace "Development aid remain in your code!!" #-}
prettyTrace ∷ Pretty a ⇒ a → b → b
prettyTrace a = trace (prettyShow a)

{-# DEPRECATED prettyTraceId "Development aid remain in your code!!" #-}
prettyTraceId ∷ Pretty a ⇒ a → a
prettyTraceId a = trace (prettyShow a) a
