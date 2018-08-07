module Test.Prune (tests) where

import qualified PGF

import Data.Maybe
import Test.Tasty
import Test.Tasty.HUnit
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Foldable
import Text.Printf

import Muste
import qualified Muste.Grammar.Internal as Grammar
import Muste.Prune

prima :: IO Grammar
prima
  = pure
  $ fromMaybe err
  $ Grammar.lookupGrammar g
  where
  g = "novo_modo/Prima"
  err = error $ printf "Could not find grammar: %s" g

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
multipleSteps :: Grammar -> Assertion
multipleSteps g = do
  let parse = Grammar.parseTTree g
      adjTs = getAdjunctionTrees g
      m     = replaceTrees g adjTs (parse "usePN Africa_PN")
      ts    = Set.map snd <$> m
      t     = parse
        $ "useCNdefsg (attribCN (useA victus_A) (useN imperium_N))"
      tslst = fold ts
  parse "useCNdefsg (useN imperium_N)" `elem` tslst @?= True
  t `elem` tslst @?= False

tests :: TestTree
tests = withResource prima mempty doTests
  where
    doTests act = testGroup "Prune" $ fmap (uncurry mkTest) testCases
      where
      mkTest :: String -> (Grammar -> Assertion) -> TestTree
      mkTest nm t = testCase nm (act >>= t)

testCases :: [(String, Grammar -> Assertion)]
testCases =
  [ "Prune suggestions that can be reached in multiple steps" |> multipleSteps
  ]
  where
    (|>) = (,)
