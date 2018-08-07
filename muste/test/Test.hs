module Main (main) where

import Test.Tasty
import Test.Tasty.QuickCheck as QC

import Data.List
import Data.Ord

import qualified Test.Prune as Prune
import qualified Test.Menu  as Menu

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests"
  [ Prune.tests
  , Menu.tests
  ]
