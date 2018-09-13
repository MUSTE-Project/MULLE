module Main (main) where

import Test.Tasty (TestTree)
import qualified Test.Tasty as Tasty

import qualified Test.Linearization as Linearization
import qualified Test.Prune         as Prune
import qualified Test.NewMenu       as NewMenu

main :: IO ()
main = Tasty.defaultMain tests

tests :: TestTree
tests = Tasty.testGroup "Tests" $
  Linearization.tests           :
  Prune.tests                   :
  NewMenu.tests                 :
  []
