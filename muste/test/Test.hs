module Main (main) where

import Test.Tasty (TestTree)
import qualified Test.Tasty as Tasty

import qualified Test.Linearization as Linearization
import qualified Test.Prune         as Prune
import qualified Test.Menu          as Menu

main :: IO ()
main = Tasty.defaultMain tests

tests :: TestTree
tests = Tasty.testGroup "Tests"
  [ Linearization.tests
  , Prune.tests
  , Menu.tests
  ]
