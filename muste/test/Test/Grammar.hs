module Test.Grammar (tests) where

import Test.Tasty
import Test.Tasty.HUnit

import Muste
import Muste.Grammar.TH as TH (tree)
import qualified Test.Common as Test

aTree ∷ TTree
aTree = Test.treeDefinite

canParse ∷ Assertion
canParse = aTree `seq` pure ()

tests ∷ TestTree
tests =
  testGroup "Grammar"
    [ "TH splice for 'TTree'" |> canParse
    ]
  where
  (|>) = testCase
