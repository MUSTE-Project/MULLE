{-# Language TemplateHaskell #-}
module Test.Prune (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Set as Set
import Data.Foldable
import Data.Set (Set)

import Muste
import Muste.Prune
import qualified Test.Common as Test
import Muste.Grammar.TH (tree)

-- | Issue #5: Should not include results that can be reached in
-- multiple steps E.g. the suggestions for
--
--     usePN Africa_PN
--
-- Should not include
--
--     useCNdefsg (attribCN (useA victus_A) (useN imperium_N))
--
-- Since it can be reached via:
--
--     useCNdefsg (useN imperium_N)
--
multipleSteps ∷ TestTree
multipleSteps = testGroup "Africa" $ mk <$> zip [0..]
  [ isSuggested    short
  , isNotSuggested long
  ]
  where
  isSuggested ∷ TTree → Assertion
  isSuggested t = t `elem` trees @?= True
  isNotSuggested ∷ TTree → Assertion
  isNotSuggested t = t `elem` trees @?= False
  mk ∷ (Int, IO ()) → TestTree
  mk (i, a) = testCase (show i) a

source ∷ TTree
source = $(tree "novo_modo/Exemplum" "usePN Africa_PN")

trees ∷ Set TTree
trees = replacements source

short ∷ TTree
short = $(tree "novo_modo/Exemplum" "(useS (useCl (simpleCl (detCN theSg_Det (useN imperium_N)) (complVA copula_V (useA magnus_A)))))")

long ∷ TTree
long = $(tree "novo_modo/Exemplum" "(useS (useCl (simpleCl (detCN theSg_Det (attribCN (useA victus_A) (useN imperium_N))) (complVA copula_V (useA magnus_A)))))")

replacements ∷ TTree → Set TTree
replacements source = fold ts
  where
  g     = Test.grammar
  adjTs = getAdjunctionTrees g
  m     = replaceTrees g adjTs source
  ts    = Set.map snd <$> m

tests ∷ TestTree
tests = testGroup "Prune" $ [multipleSteps]
  -- [ testCase "Multiple steps" multipleSteps ]
