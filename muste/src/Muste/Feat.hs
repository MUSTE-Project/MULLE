{- |
  Original Author: Koen Claesson
  Original License: BSD (2-clause)
  Original URL: https://github.com/koengit/grammarfeat
  Adopted by Herbert Lange for Muste
-}
{-# Language OverloadedStrings #-}
module Muste.Feat
  ( mkFEAT
  , featCard
  , featIth
  , emptyFeat
  , getRuleType
  , getAllRules
  , generateTrees
  ) where

import Prelude ()
import Muste.Prelude
import Data.List

import Muste.Grammar.Internal
  (Rule(Function), getAllRules, Grammar, getRuleType)
import Muste.Tree

type FEAT = Category -> Int -> (Integer, Integer -> TTree)

emptyFeat :: Category -> Int -> (Integer, Integer -> TTree)
emptyFeat _ _ = (-1, \_ -> TMeta "*empty*")
             
-- | Compute how many trees there are of a given size and type.
featCard :: FEAT -> Category -> Int -> Integer
featCard f c n = fst (f c n)

-- | Generate the i-th tree of a given size and type.
featIth :: FEAT -> Category -> Int -> Integer -> TTree
featIth f c n = snd (f c n)

mkFEAT :: Grammar -> FEAT
mkFEAT gr =
  \c s -> let (n,h) = catList [c] s in (n, head . h)
 where
   catList' :: [Category] -> Int -> (Integer, Integer -> [TTree])
   catList' [] s =
     if s == 0
     then (1, \0 -> [])
     else (0, error "empty")
   catList' [c] s =
     parts ( [(1, \_ -> [TMeta c]) | s == 1 ]
             ++
           [ (n, \i -> [TNode f t (h i)])
           | s > 0 
           , (Function f t) <- getAllRules gr
           , let (Fun y xs) = t
           , y == c
           , let (n,h) = catList xs (s-1)
          ])
   catList' (c:cs) s =
     parts [ (nx*nxs, \i -> hx (i `mod` nx) ++ hxs (i `div` nx))
           | k <- [0..s]
           , let (nx,hx)   = catList [c] k
                 (nxs,hxs) = catList cs (s-k)
           ]
   catList ∷ [Category] → Int → (Integer, Integer → [TTree])
   catList = memo catList'
     where
       cats :: [Category]
       cats = nub [ x | r <- getAllRules gr, let (Fun y xs) = getRuleType r, x <- y:xs ]
       memo :: ([Category] -> Int -> (Integer, Integer -> [TTree])) -> ([Category] -> Int -> (Integer, Integer -> [TTree]))
       memo f = \case
         []   -> (nil !!)
         a:as -> head [ f' as | (c,f') <- cons, a == c ]
         where
           nil  = [ f [] s | s <- [0..] ]
           cons = [ (c, memo (f . (c:))) | c <- cats ]
   parts :: [(Integer, Integer -> [TTree])] -> (Integer, Integer -> [TTree])
   parts []          = (0, error "empty parts ")
   parts ((n,h):nhs) = (n+n', \i -> if i < n then h i else h' (i-n))
     where
       (n',h') = parts nhs

-- | The function 'generateTrees' generates a list of 'TTree's up to a certain depth given a grammar. Powered by the magic of feat
generateTrees :: FEAT -> Category -> [[TTree]]
generateTrees f cat =
  let
    feats = map (\d -> (featCard f cat d,featIth f cat d)) [0..]
  in
    map (\(m,fs) -> map fs [0..m-1]) feats


