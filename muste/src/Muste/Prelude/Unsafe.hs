{-# OPTIONS_GHC -Wall -Wcompat #-}
module Muste.Prelude.Unsafe where

import Prelude hiding (head, read, (!!), undefined)
-- We could maybe emit a warning when using these?
import qualified Prelude as Unsafe
import qualified Data.Maybe as Unsafe

-- Use pattern-matching, 'listToMaybe' or the version from 'NonEmpty'.
head ∷ [a] → a
head = Unsafe.head

-- Use 'readMaybe', 'readEither' os similiar.  And while youre at it,
-- maybe you want to switch to 'Text'?
read ∷ Read a ⇒ String → a
read = Unsafe.read

-- You probably want a vector/array.
(!!) ∷ [a] → Int → a
(!!) = (Unsafe.!!)

-- Use 'error'
undefined ∷ a
undefined = Unsafe.undefined

foldl1 ∷ Foldable f ⇒ (a → a → a) → f a → a
foldl1 = Unsafe.foldl1

tail ∷ [a] → [a]
tail = Unsafe.tail

fromJust ∷ Maybe a → a
fromJust = Unsafe.fromJust
