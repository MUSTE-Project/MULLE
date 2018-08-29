{-# OPTIONS_GHC -Wno-name-shadowing #-}
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
  , lookupFail
  , renderDoc
  , putDoc
  , putDocLn
  , lookupFailIO
  , traceShowId
  ) where

import Control.Monad.IO.Class
import Control.Exception
import Prelude hiding (fail)
import qualified Data.Set as Set
import Data.List (groupBy)
import Data.Function (on)
import Control.Monad.Fail
import Text.Read (readEither)
import Data.Binary (Binary)
import qualified Data.Binary as Binary
import Data.ByteString.Lazy (ByteString)
import Data.String.Conversions (ConvertibleStrings(convertString))
import qualified Data.Containers as Mono
import Data.Containers (IsMap)
import Data.Text.Prettyprint.Doc (Doc, Pretty, layoutCompact)
import qualified Data.Text.Prettyprint.Doc as Doc
import Data.Text.Prettyprint.Doc.Render.String (renderString)

import qualified Debug.Trace

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

readFail ∷ Read r ⇒ MonadFail m ⇒ String → m r
readFail = eitherFail . readEither

eitherFail ∷ MonadFail m ⇒ Either String a → m a
eitherFail = \case
  Left s → fail s
  Right a → pure a

enumerate ∷ [a] → [(Int, a)]
enumerate = zip [0..]

maybeFail ∷ MonadFail m ⇒ String → Maybe a → m a
maybeFail err = \case
  Nothing → fail err
  Just a → pure a

maybeFailIO ∷ MonadIO m ⇒ Exception e ⇒ e → Maybe a → m a
maybeFailIO err = \case
  Nothing → liftIO $ throwIO err
  Just a → pure a

binaryToText :: Binary bin ⇒ ConvertibleStrings ByteString text ⇒ bin → text
binaryToText = convertString . Binary.encode

binaryFromText :: Binary bin ⇒ ConvertibleStrings text ByteString ⇒ text → bin
binaryFromText = Binary.decode . convertString


-- * Debug aids

{-# DEPRECATED trace "Development aid remain in your code!!" #-}
trace ∷ String → a → a
trace = Debug.Trace.trace

{-# DEPRECATED traceShow "Development aid remain in your code!!" #-}
traceShow ∷ Show a ⇒ a → b → b
traceShow = Debug.Trace.traceShow

{-# DEPRECATED traceShowId "Development aid remain in your code!!" #-}
traceShowId ∷ Show a ⇒ a → a
traceShowId = Debug.Trace.traceShowId

prettyShow ∷ Pretty a => a → String
prettyShow = show . Doc.pretty

{-# DEPRECATED prettyTrace "Development aid remain in your code!!" #-}
prettyTrace ∷ Pretty a ⇒ a → b → b
prettyTrace a = trace (prettyShow a)

{-# DEPRECATED prettyTraceId "Development aid remain in your code!!" #-}
prettyTraceId ∷ Pretty a ⇒ a → a
prettyTraceId a = trace (prettyShow a) a

-- | Useful in concert with TypeApplications during development.
{-# DEPRECATED from "Development aid remain in your code!!" #-}
from ∷ ∀ a b . a → b
from = undefined

-- | Useful in concert with TypeApplications during development.
{-# DEPRECATED to "Development aid remain in your code!!" #-}
to ∷ ∀ a b . b → a
to = undefined

lookupFail
  ∷ MonadFail m
  ⇒ IsMap map
  ⇒ String
  → Mono.ContainerKey map
  → map
  → m (Mono.MapValue map)
lookupFail err k = maybeFail err . Mono.lookup k

lookupFailIO
  ∷ MonadIO m
  ⇒ IsMap map
  ⇒ Exception e
  ⇒ e
  → Mono.ContainerKey map
  → map
  → m (Mono.MapValue map)
lookupFailIO err k = maybeFailIO err . Mono.lookup k

renderDoc ∷ Doc a → String
renderDoc = renderString . layoutCompact

putDoc ∷ Doc a → IO ()
putDoc = putStr . renderDoc

putDocLn ∷ Doc a → IO ()
putDocLn = putStrLn . renderDoc
