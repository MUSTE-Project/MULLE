module Muste.Common
  ( preAndSuffix
  , wildCard
  , noDuplicates
  , areDisjoint
  , isSubList
  ) where

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
noDuplicates (x:y:zs)
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
