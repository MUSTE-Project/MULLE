{-
  Original Author: Koen Claesson
  Original License: BSD (2-clause)
  Original URL: https://github.com/koengit/grammarfeat
  Adopted by Herbert Lange for Muste
-}
module Muste.Feat(Grammar(..),Rule(..),FunType(..),TTree(..),mkFEAT,featCard,featIth,emptyFeat,getRuleType,getAllRules) where

import Data.List
import Data.Maybe
import Data.Char
import qualified Data.Set as S

import PGF

--------------------------------------------------------------------------------
-- grammar types

-- | Type 'FunType' consists of a String that is the the result category and [String] are the parameter categories
data FunType = Fun String [String] | NoType deriving (Ord,Eq,Show,Read)

-- | Type 'Rule' consists of a String as the function name and a 'FunType' as the Type
data Rule = Function String FunType deriving (Ord,Eq,Show,Read)

-- | Type 'Grammar' consists of a start categorie and a list of rules
data Grammar = Grammar {
  startcat :: String,
  synrules :: [Rule],
  lexrules :: [Rule],
  pgf :: PGF,
  feat :: FEAT
  }

-- | The function 'getRules' returns the union of syntactic and lexical rules of a grammar
getAllRules :: Grammar -> [Rule]
getAllRules g = union (synrules g) (lexrules g)

-- | The function 'getRuleType' extracts the full type of a rule
getRuleType :: Rule -> FunType
getRuleType (Function _ funType) = funType

--------------------------------------------------------------------------------

-- tree

-- | A generic tree with types
data TTree = TNode String FunType [TTree] -- Regular node consisting of a function name, function type and possible subtrees
           | TMeta String -- A meta tree consisting just of a category type
           deriving (Ord,Eq,Show,Read) -- read is broken at the moment, most likely because of the CId


-- FEAT-style generator magic

type FEAT = String -> Int -> (Integer, Integer -> TTree)

emptyFeat :: String -> Int -> (Integer, Integer -> TTree)
emptyFeat = \_ _ -> (-1, \_ -> TMeta "*empty*")
             
-- compute how many trees there are of a given size and type
featCard :: FEAT -> String -> Int -> Integer
featCard f c n = fst (f c n)

-- generate the i-th tree of a given size and type
featIth :: FEAT -> String -> Int -> Integer -> TTree
featIth f c n i = snd (f c n) i

mkFEAT :: Grammar -> FEAT
mkFEAT gr =
  \c s -> let (n,h) = catList [c] s in (n, head . h)
 where
   catList' :: [String] -> Int -> (Integer, Integer -> [TTree])
   catList' [] s =
     if s == 0
     then (1, \0 -> [])
     else (0, error "empty")

   catList' [c] s =
     parts [ (n, \i -> [TNode f t (h i)])
           | s > 0 
           , r@(Function f t) <- getAllRules gr
           , let (Fun y xs) = t
           , y == c
           , let (n,h) = catList xs (s-1)
          ]

   catList' (c:cs) s =
     parts [ (nx*nxs, \i -> hx (i `mod` nx) ++ hxs (i `div` nx))
           | k <- [0..s]
           , let (nx,hx)   = catList [c] k
                 (nxs,hxs) = catList cs (s-k)
           ]

   catList = memo catList'
     where
       cats :: [String]
       cats = nub [ x | r <- getAllRules gr, let (Fun y xs) = getRuleType r, x <- y:xs ]
       memo :: ([String] -> Int -> (Integer, Integer -> [TTree])) -> ([String] -> Int -> (Integer, Integer -> [TTree]))
       memo f = \cs -> case cs of
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

--------------------------------------------------------------------------------

