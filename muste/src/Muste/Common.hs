{-# Language UnicodeSyntax, FlexibleContexts #-}
module Muste.Common
  ( preAndSuffix
  , wildCard
  , noDuplicates
  , areDisjoint
  , isSubList
  , editDistance
  , groupOn
  , groupOnSingle
  , isSubListOf
  , prettyShow
  , prettyTrace
  , prettyTraceId
  , readFail
  , eitherFail
  , enumerate
  , maybeFail
  , binaryFromText
  , binaryToText
  ) where

import Prelude hiding (fail)
import qualified Data.Set as Set
import Data.List (groupBy)
import Data.Function (on)
import Data.Text.Prettyprint.Doc (Pretty)
import qualified Data.Text.Prettyprint.Doc as Doc
import Control.Monad.Fail
import Text.Read (readEither)
import Data.Binary (Binary)
import qualified Data.Binary as Binary
import Data.ByteString.Lazy (ByteString)
import Data.String.Conversions (ConvertibleStrings(convertString))

import Debug.Trace

-- Computes the longest common prefix and suffix for linearized trees
preAndSuffix :: Eq a => [a] -> [a] -> ([a],[a])
preAndSuffix [] _  = ([],[])
preAndSuffix _  [] = ([],[])
preAndSuffix a b =
  let prefix :: Eq a => [a] -> [a] ->([a],[a])
      prefix [] _ = ([],[])
      prefix _ [] = ([],[])
      prefix (a:resta) (b:restb)
        | a == b = let (pre,suf) = prefix resta restb in (a:pre,suf)
        | otherwise = ([],reverse $ postfix (reverse (a:resta)) (reverse (b:restb)))
      postfix :: Eq a => [a] -> [a] -> [a]
      postfix [] _ = []
      postfix _ [] = []
      postfix (a:resta) (b:restb)
        | a == b = let suf = postfix resta restb in (a:suf)
        | otherwise = []
  in
    prefix a b

wildCard :: String
wildCard = "*empty*"

-- | True if the (ordered) list contains no duplicates (i.e., is a set)
noDuplicates :: Eq a => [a] -> Bool
noDuplicates (x:y:_)
  | x == y = False
  | otherwise = error "Prune.noDuplicates: Non-exhaustive guard statement"
noDuplicates (_:zs) = noDuplicates zs
noDuplicates _ = True

-- | True if the (ordered) list (without duplicated) are disjoint
areDisjoint :: Ord a => [a] -> [a] -> Bool
areDisjoint xs@(x:xs') ys@(y:ys')
    | x == y = False
    | x < y = areDisjoint xs' ys
    | otherwise = areDisjoint xs ys'
areDisjoint _ _ = True

-- | @'isSubList' c d@ Check if all elements in @c@ also occur in @d@
-- (in the same order).
isSubList :: Eq a => [a] -> [a] -> Bool
isSubList [] _ = True
isSubList _ [] = False
isSubList csub@(c:sub) (d:super) | c == d    = isSubList sub super
                                 | otherwise = isSubList csub super

-- | Levenshtein distance between two lists, taken from
-- <https://wiki.haskell.org/Edit_distance>
editDistance :: Eq a => [a] -> [a] -> Int
editDistance a b = last (if lab == 0 then mainDiag
                         else if lab > 0 then lowers !! (lab - 1)
                              else {- < 0 -}  uppers !! (-1 - lab))
    where mainDiag = oneDiag a b (head uppers) (-1 : head lowers)
          uppers   = eachDiag a b (mainDiag : uppers) -- upper diagonals
          lowers   = eachDiag b a (mainDiag : lowers) -- lower diagonals
          eachDiag _ [] _ = []
          eachDiag a (_:bs) (lastDiag:diags) = oneDiag a bs nextDiag lastDiag : eachDiag a bs diags
              where nextDiag = head (tail diags)
          eachDiag _ _ _ = error "Common.editDistance: Unmatched clause"
          oneDiag a b diagAbove diagBelow = thisdiag
              where doDiag [] _b _nw _n _w = []
                    doDiag _a [] _nw _n _w = []
                    doDiag (ach:as) (bch:bs) nw n w = me : doDiag as bs me (tail n) (tail w)
                        where me = if ach == bch then nw else 1 + min3 (head w) nw (head n)
                    firstelt = 1 + head diagBelow
                    thisdiag = firstelt : doDiag a b firstelt diagAbove (tail diagBelow)
          lab = length a - length b
          min3 x y z = if x < y then x else min y z

-- | 'groupOn p' groups a list by using the 'Eq' instance of the
-- projection @p@.
groupOn ∷ Eq b ⇒ (a → b) → [a] → [[a]]
groupOn p = groupBy ((==) `on` p)

-- NB: Even though we're using the unsafe method 'head' we shuold be
-- safe since 'groupOn' should not return any empty lists.
-- | Like 'groupOn' but just with a single element from each
-- group.
groupOnSingle ∷ Eq b ⇒ (a → b) → [a] → [a]
groupOnSingle p = map head . groupOn p

-- | @'isSublistOf' xs ys@ checks if @xs@ is a sub list (disregarding
-- the order) of @ys@.
isSubListOf ∷ Ord a ⇒ Eq a ⇒ [a] → [a] → Bool
isSubListOf = Set.isSubsetOf `on` Set.fromList

prettyShow ∷ Pretty a => a → String
prettyShow = show . Doc.pretty

{-# Deprecated prettyTrace "'prettyTrace' remains in your code. Pls fix!" #-}
prettyTrace ∷ Pretty a ⇒ a → b → b
prettyTrace a = trace (prettyShow a)

{-# Deprecated prettyTraceId "'prettyTraceId' remains in your code. Pls fix!" #-}
prettyTraceId ∷ Pretty a ⇒ a → a
prettyTraceId a = trace (prettyShow a) a

readFail ∷ Read r ⇒ MonadFail m ⇒ String → m r
readFail = eitherFail . readEither

eitherFail ∷ MonadFail m ⇒ Either String a → m a
eitherFail = \case
  Left s → fail s
  Right a → pure a

enumerate ∷ [a] → [(Int, a)]
enumerate = zipWith (,) [0..]

maybeFail ∷ MonadFail m ⇒ String → Maybe a → m a
maybeFail err = \case
  Nothing → fail err
  Just a → pure a

binaryToText :: Binary bin ⇒ ConvertibleStrings ByteString text ⇒ bin → text
binaryToText = convertString . Binary.encode

binaryFromText :: Binary bin ⇒ ConvertibleStrings text ByteString ⇒ text → bin
binaryFromText = Binary.decode . convertString
