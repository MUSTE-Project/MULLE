{-# Language TemplateHaskell #-}
module Test.Prune (tests) where

import Data.Maybe
import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Set as Set
import Data.Foldable
import Text.Printf
import Data.Set (Set)

import Muste
import qualified Muste.Grammar.Internal as Grammar
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
  [ isSuggested $(tree "novo_modo/Exemplum" "useCNdefsg (useN imperium_N)")
  , isNotSuggested defsg
  ]
  where
  source = $(tree "novo_modo/Exemplum" "usePN Africa_PN")
  trees = replacements source
  isSuggested ∷ TTree → Assertion
  isSuggested t = t `elem` trees @?= True
  isNotSuggested ∷ TTree → Assertion
  isNotSuggested t = t `elem` trees @?= False
  mk (i, a) = testCase (show i) a

parse = Grammar.parseTTree Test.grammar

replacements ∷ TTree → Set TTree
replacements source = fold ts
  where
  g     = Test.grammar
  adjTs = getAdjunctionTrees g
  m     = replaceTrees g adjTs source
  ts    = Set.map snd <$> m

-- Used to be
--
--     useCNdefsg (attribCN (useA victus_A) (useN imperium_N))
--
-- But since the test grammar changed this one does not exist anymore.
defsg ∷ TTree
-- defsg = $(tree "novo_modo/Exemplum" "detCN multus_Det (useN imperium_N)")
defsg = $(tree "novo_modo/Exemplum" "useCNdefsg (attribCN (useA victus_A) (useN imperium_N))")

tests ∷ TestTree
tests = testGroup "Prune" $ [multipleSteps]
  -- [ testCase "Multiple steps" multipleSteps ]
