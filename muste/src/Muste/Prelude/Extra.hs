{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
{-# Language
 CPP,
 FlexibleContexts,
 OverloadedStrings
#-}

module Muste.Prelude.Extra
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
  , maybeThrow
  , binaryFromText
  , binaryToText
  , lookupFail
  , renderDoc
  , putDoc
  , putDocLn
  , lookupFailIO
  , lookupThrow
  , trace
  , traceShow
  , traceShowId
  , decodeFileThrow
  , throwLeft
  ) where

import Control.Monad.Catch (MonadThrow(throwM))
import Control.Exception (Exception, throwIO, throw)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Data.Function ((&), on)

import Data.Aeson (FromJSON)
import qualified Data.Set as Set
import Data.Binary (Binary)
import qualified Data.Binary as Binary
import Data.ByteString.Lazy (ByteString)
import Data.String.Conversions (ConvertibleStrings(convertString))
import qualified Data.Containers as Mono
import Data.Containers (IsMap)
import Data.String (IsString)
import Data.Text (Text)
import Data.Text.Prettyprint.Doc (Doc, Pretty)
import qualified Data.Text.Prettyprint.Doc as Doc
import Data.Text.Prettyprint.Doc.Render.String (renderString)
import qualified Data.Text.Prettyprint.Doc.Render.Text as Doc
import Text.Read (readEither)
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty, groupBy)
import qualified Data.Yaml as Yaml

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

wildCard :: IsString text => text
wildCard = "*empty*"

{-# Specialize wildCard :: Text #-}
{-# Specialize wildCard :: String #-}

-- | True if the (ordered) list contains no duplicates (i.e., is a set)
noDuplicates :: Eq a => [a] -> Bool
noDuplicates (x:y:_)
  | x == y = False
  | otherwise = error "Prune.noDuplicates: Non-exhaustive guard statement"
noDuplicates (_:zs) = noDuplicates zs
noDuplicates _ = True

-- | True if the (ordered) list (without duplicated) are disjoint
areDisjoint :: Ord a => [a] -> [a] -> Bool
areDisjoint xs ys
  = Set.intersection (Set.fromList xs) (Set.fromList ys)
  & Set.null

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

groupOn :: Eq b => (a -> b) -> [a] -> [NonEmpty a]
groupOn p = groupBy ((==) `on` p)

-- | Like 'groupOn' but just with a single element from each group.
groupOnSingle :: Eq b => (a -> b) -> [a] -> [a]
groupOnSingle p = map NonEmpty.head . groupOn p

-- | @'isSublistOf' xs ys@ checks if @xs@ is a sub list (disregarding
-- the order) of @ys@.
isSubListOf :: Ord a => Eq a => [a] -> [a] -> Bool
isSubListOf = Set.isSubsetOf `on` Set.fromList

readFail :: Read r => Monad m => String -> m r
readFail = eitherFail . readEither

eitherFail :: Monad m => Either String a -> m a
eitherFail (Left  s) = fail s
eitherFail (Right a) = pure a

enumerate :: [a] -> [(Int, a)]
enumerate = zip [0..]

maybeFail :: Monad m => String -> Maybe a -> m a
maybeFail err Nothing = fail err
maybeFail _  (Just a) = pure a

maybeFailIO :: MonadIO m => Exception e => e -> Maybe a -> m a
maybeFailIO err Nothing = liftIO $ throwIO err
maybeFailIO _  (Just a) = pure a

maybeThrow :: MonadThrow m => Exception e => e -> Maybe a -> m a
maybeThrow err Nothing = throwM err
maybeThrow _  (Just a) = pure a

binaryToText :: Binary bin => ConvertibleStrings ByteString text => bin -> text
binaryToText = convertString . Binary.encode

binaryFromText :: Binary bin => ConvertibleStrings text ByteString => text -> bin
binaryFromText = Binary.decode . convertString


-- * Debug aids

{-# DEPRECATED trace "Development aid remain in your codeUnsafe.!!" #-}
trace :: String -> a -> a
trace = Debug.Trace.trace

{-# DEPRECATED traceShow "Development aid remain in your codeUnsafe.!!" #-}
traceShow :: Show a => a -> b -> b
traceShow = Debug.Trace.traceShow

{-# DEPRECATED traceShowId "Development aid remain in your codeUnsafe.!!" #-}
traceShowId :: Show a => a -> a
traceShowId = Debug.Trace.traceShowId

prettyShow :: Pretty a => a -> String
prettyShow = show . Doc.pretty

{-# DEPRECATED prettyTrace "Development aid remain in your codeUnsafe.!!" #-}
prettyTrace :: Pretty a => a -> b -> b
prettyTrace a = trace (prettyShow a)

{-# DEPRECATED prettyTraceId "Development aid remain in your codeUnsafe.!!" #-}
prettyTraceId :: Pretty a => a -> a
prettyTraceId a = trace (prettyShow a) a

lookupFail
  :: Monad m
  => IsMap map
  => String
  -> Mono.ContainerKey map
  -> map
  -> m (Mono.MapValue map)
lookupFail err k = maybeFail err . Mono.lookup k

lookupFailIO
  :: MonadIO m
  => IsMap map
  => Exception e
  => e
  -> Mono.ContainerKey map
  -> map
  -> m (Mono.MapValue map)
lookupFailIO err k = maybeFailIO err . Mono.lookup k

lookupThrow
  :: MonadThrow m
  => IsMap map
  => Exception e
  => e
  -> Mono.ContainerKey map
  -> map
  -> m (Mono.MapValue map)
lookupThrow e k = maybeThrow e . Mono.lookup k

renderDoc :: Doc a -> String
renderDoc = renderString . Doc.layoutPretty Doc.defaultLayoutOptions

putDoc :: Doc a -> IO ()
putDoc = Doc.putDoc

putDocLn :: Doc a -> IO ()
putDocLn = putDoc . (<> Doc.line)

decodeFileThrow :: MonadIO m => FromJSON a => FilePath -> m a
-- #if MIN_VERSION_yaml(0,8,31)
decodeFileThrow = Yaml.decodeFileThrow
-- #else
-- decodeFileThrow f
--   = liftIO $ Yaml.decodeFileEither f >>= either throwIO return
-- #endif

-- | Throws an exception if the it's a 'Left' (requires the left to be
-- an exception).  This method is *unsafe*!
throwLeft :: Exception e => Either e c -> c
throwLeft = either throw (\x -> x)
