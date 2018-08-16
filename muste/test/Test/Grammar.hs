{-# Language TemplateHaskell #-}
module Test.Grammar (tests) where

import Test.Tasty
import Test.Tasty.HUnit

import Muste
import Muste.Grammar.TH as TH (tree)

aTree ∷ TTree
aTree = $(TH.tree "novo_modo/Prima" "useS (useCl (simpleCl (useCNindefsg (useN hostis_N)) (transV vincere_V2 (usePN Africa_PN))))" )

tests ∷ TestTree
tests =
  testGroup "Grammar"
    [ "TH splice for 'TTree'" |> canCompile
    ]
  where
  (|>) = testCase
  canCompile ∷ Assertion
  canCompile = pure ()
