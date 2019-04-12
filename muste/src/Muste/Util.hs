{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
{-# Language
 FlexibleContexts,
 OverloadedStrings
#-}

module Muste.Util
  ( wildCard
  , editDistance
  , binaryFromText
  , binaryToText
  , lookupFail
  , putDocLn
  ) where


import Data.Binary (Binary)
import qualified Data.Binary as Binary
import Data.ByteString.Lazy (ByteString)
import Data.String.Conversions (ConvertibleStrings(convertString))
import qualified Data.Containers as Mono
import Data.Containers (IsMap)
import Data.String (IsString)
import Data.Text (Text)
import Data.Text.Prettyprint.Doc (Doc)
import qualified Data.Text.Prettyprint.Doc as Doc
import qualified Data.Text.Prettyprint.Doc.Render.Text as Doc

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

maybeFail :: Monad m => String -> Maybe a -> m a
maybeFail err Nothing = fail err
maybeFail _  (Just a) = pure a

binaryToText :: Binary bin => ConvertibleStrings ByteString text => bin -> text
binaryToText = convertString . Binary.encode

binaryFromText :: Binary bin => ConvertibleStrings text ByteString => text -> bin
binaryFromText = Binary.decode . convertString

lookupFail
  :: Monad m
  => IsMap map
  => String
  -> Mono.ContainerKey map
  -> map
  -> m (Mono.MapValue map)
lookupFail err k = maybeFail err . Mono.lookup k

putDoc :: Doc a -> IO ()
putDoc = Doc.putDoc

putDocLn :: Doc a -> IO ()
putDocLn = putDoc . (<> Doc.line)
