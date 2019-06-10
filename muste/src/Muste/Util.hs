{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
{-# Language
 FlexibleContexts,
 OverloadedStrings
#-}

module Muste.Util
  ( wildCard
  , editDistance
  ) where

import Data.String (IsString)
import Data.Text (Text)

wildCard :: IsString text => text
wildCard = "*empty*"

{-# Specialize wildCard :: Text #-}
{-# Specialize wildCard :: String #-}

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

