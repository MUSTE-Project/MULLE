{- | Implements several tests to control the validy of the program
-}
module Test.Muste where
import PGF
import PGF.Internal
import Muste.Grammar.Internal
import Muste.Tree
import Muste
import Test.HUnit.Text
import Test.HUnit.Base
import Data.Maybe
import qualified Data.Map as M
import Control.Monad
import Data.Set (Set(..),empty,fromList)
import Test.QuickCheck
import Test.Framework
import Test.Data

-- HUnit tests
  
hunit_linearizeTree_test =
  -- The 'linearizeTree' function linearizes a MetaTTree to a list of tokens and pathes to the nodes that create it
  -- linearizeTree :: Grammar -> Language -> MetaTTree ->  [LinToken]
  let
    pgf = readPGF "gf/ABCAbs.pgf"
    grammar = fmap pgfToGrammar pgf
    -- tree1 is in Test.Data
    tree2 = TNode "a" (Fun "A" []) [] -- MetaTTree (read "{a:A}") empty
    tree3 = TNode "s" (Fun "S" ["A"]) [TNode "a" (Fun "A" []) []] -- MetaTTree (read "{s:(A->S) {a:A}}") empty
    tree4 = TNode "s" (Fun "S" ["A"]) [TNode "f" (Fun "A" ["A","B"]) [TMeta "A", TNode "b" (Fun "B" []) []]] -- MetaTTree (read "{s:(A->S) {f:(A->B->A) {?A} {b:B}}}") empty
    tree5 = TNode "s" (Fun "S" ["A"]) [TNode "f" (Fun "A" ["A","B"]) [TNode "a" (Fun "A" []) [],TMeta "B"]] -- MetaTTree (read "{s:(A->S) {f:(A->B->A) {a:A} {?B}}}") empty
    tree6 = TNode "s" (Fun "S" ["A"]) [TNode "f" (Fun "A" ["A","B"]) [TMeta "A",TMeta "B"]] -- MetaTTree (read "{s:(A->S) {f:(A->B->A) {?A} {?B}}}") empty
    tree7 = TNode "s" (Fun "S" ["A"]) [TNode "f" (Fun "A" ["A","B"]) [TNode "a" (Fun "A" []) [], TNode "b" (Fun "B" []) []]] -- MetaTTree (read "{s:(A->S) {f:(A->B->A) {a:A} {b:B}}}") empty
    tree8 = TNode "s" (Fun "S" ["A"]) [TNode "h" (Fun "A" ["A","A","A"]) [TNode "a" (Fun "A" []) [],TNode "a" (Fun "A" []) [],TNode "a" (Fun "A" []) []]] -- MetaTTree (read "{s:(A->S) {h:(A->A->A->A) {a:A} {a:A} {a:A}}}") empty
  in
    TestList [
    TestLabel "Empty Grammar" (linearizeTree emptyGrammar (mkCId "ABC1") tree2 ~?= [([],"?0")]),
    TestLabel "Empty Lang" ( TestCase $ grammar >>= (\g -> linearizeTree g wildCId tree1 @?= [([],"?0")]) ),
    TestLabel "Meta node" ( TestCase $ grammar >>= (\g -> linearizeTree g (mkCId "ABC1") tree1 @?= [([],"?0")]) ),
    TestLabel "Simple node" ( TestCase $ grammar >>= (\g -> linearizeTree g (mkCId "ABC1") tree2 @?= [([],"a")]) ),
    TestLabel "Simple tree" ( TestCase $ grammar >>= (\g -> linearizeTree g (mkCId "ABC1") tree3 @?= [([0],"a")]) ),
    TestLabel "Tree 1" ( TestCase $ grammar >>= (\g -> linearizeTree g (mkCId "ABC1") tree4 @?= [([0,0],"?0"),([0],"x"),([0,1],"b")]) ),
    TestLabel "Tree 2" ( TestCase $ grammar >>= (\g -> linearizeTree g (mkCId "ABC1") tree5 @?= [([0,0],"a"),([0],"x"),([0,1],"?0")]) ),
    TestLabel "Tree 3" ( TestCase $ grammar >>= (\g -> linearizeTree g (mkCId "ABC1") tree6 @?= [([0,0],"?0"),([0],"x"),([0,1],"?1")]) ),
    TestLabel "Tree 4" (TestCase $ grammar >>= (\g -> linearizeTree g (mkCId "ABC1") tree7 @?= [([0,0],"a"),([0],"x"),([0,1],"b")]) ),
    TestLabel "Tree 5" ( TestCase $ grammar >>= (\g -> linearizeTree g (mkCId "ABC1") tree8 @?= [([0,0],"a"),([0,1],"a"),([0,2],"a")]))
    ]

hunit_preAndSuffix_test = -- TODO
  -- -- Computes the longest common prefix and suffix for linearized trees
  -- preAndSuffix :: Eq a => [a] -> [a] -> ([a],[a])
  TestList [
--  TestLabel "fail" (TestCase $ assertFailure "intended fail")
  ]
  
hunit_getSuggestions_test = -- TODO
-- The 'getSuggestions' function generates a list of similar trees given a tree and a position in the token list
-- getSuggestions :: Grammar -> Language -> [LinToken] -> MetaTTree -> Pos -> S.Set String
  TestList [
  ]

-- QuickCheck tests

various_tests = TestList [
  TestLabel "preAndSuffix" hunit_preAndSuffix_test
  ]
  
linearize_tests = TestList [
  TestLabel "linearizeTree" hunit_linearizeTree_test
  ]

suggestion_tests =
  TestList [
  -- TestLabel "getNewTrees" hunit_getNewTrees_test, -- This test takes too long at the moment
  TestLabel "getSuggestions" hunit_getSuggestions_test
  ]

hunit_tests = TestList [various_tests,linearize_tests, suggestion_tests]

quickcheck_tests :: [(TestName,Property)]
quickcheck_tests = [
  ]
