module Common (showPretty, tracePretty, tracePrettyId, traceShowId) where

import Data.Text.Prettyprint.Doc (Pretty)
import qualified Data.Text.Prettyprint.Doc as Doc

import qualified Debug.Trace as Debug

{-# DEPRECATED traceShowId "Development aid remain in your code!!" #-}
traceShowId ∷ Show a ⇒ a → a
traceShowId = Debug.traceShowId

showPretty ∷ Pretty a => a → String
showPretty = show . Doc.pretty

{-# DEPRECATED tracePretty "Development aid remain in your code!!" #-}
tracePretty ∷ Pretty a ⇒ a → b → b
tracePretty a = Debug.trace (showPretty a)

{-# DEPRECATED tracePrettyId "Development aid remain in your code!!" #-}
tracePrettyId ∷ Pretty a ⇒ a → a
tracePrettyId a = Debug.trace (showPretty a) a
