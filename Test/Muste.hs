{- | Implements several tests to control the validy of the program
-}
module Test.Muste where
import PGF
import PGF.Internal
import Muste.Grammar
import Muste.Tree
import Muste
import Test.HUnit.Text
import Test.HUnit.Base
import Data.Maybe
import qualified Data.Map as M
import Control.Monad
import Data.Set (Set(..),empty,fromList)

-- HUnit tests

hunit_linearizeTree_test =
  -- The 'linearizeTree' function linearizes a MetaTTree to a list of tokens and pathes to the nodes that create it
  -- linearizeTree :: Grammar -> Language -> MetaTTree ->  [LinToken]
  let
    pgf = readPGF "gf/ABCAbs.pgf"
    grammar = pgf >>= (\p -> return $ pgfToGrammar p)
    tree1 = MetaTTree (read "{?A}") $ empty
    tree2 = MetaTTree (read "{a:A}") $ empty
    tree3 = MetaTTree (read "{s:(A->S) {a:A}}") $ empty
    tree4 = MetaTTree (read "{s:(A->S) {f:(A->B->A) {?A} {b:B}}}") $ empty
    tree5 = MetaTTree (read "{s:(A->S) {f:(A->B->A) {a:A} {?B}}}") $ empty
    tree6 = MetaTTree (read "{s:(A->S) {f:(A->B->A) {?A} {?B}}}") $ empty
    tree7 = MetaTTree (read "{s:(A->S) {f:(A->B->A) {a:A} {b:B}}}") $ empty
    tree8 = MetaTTree (read "{s:(A->S) {h:(A->A->A->A) {a:A} {a:A} {a:A}}}") $ empty
  in
    TestList [
    TestLabel "Meta node" $ TestCase $ grammar >>= (\g -> linearizeTree g (mkCId "ABC1") tree1 @?= [([],"?0")]),
    TestLabel "Simple node" $ TestCase $ grammar >>= (\g -> linearizeTree g (mkCId "ABC1") tree2 @?= [([],"a")]),
    TestLabel "Simple tree" $ TestCase $ grammar >>= (\g -> linearizeTree g (mkCId "ABC1") tree3 @?= [([0],"a")]),
    TestLabel "Tree 1" $ TestCase $ grammar >>= (\g -> linearizeTree g (mkCId "ABC1") tree4 @?= [([0,0],"?0"),([0],"x"),([0,1],"b")]),
    TestLabel "Tree 2" $ TestCase $ grammar >>= (\g -> linearizeTree g (mkCId "ABC1") tree5 @?= [([0,0],"a"),([0],"x"),([0,1],"?0")]),
    TestLabel "Tree 3" $ TestCase $ grammar >>= (\g -> linearizeTree g (mkCId "ABC1") tree6 @?= [([0,0],"?0"),([0],"x"),([0,1],"?1")]),
    TestLabel "Tree 4" $ TestCase $ grammar >>= (\g -> linearizeTree g (mkCId "ABC1") tree7 @?= [([0,0],"a"),([0],"x"),([0,1],"b")]),
    TestLabel "Tree 5" $ TestCase $ grammar >>= (\g -> linearizeTree g (mkCId "ABC1") tree8 @?= [([0,0],"a"),([0,1],"a"),([0,2],"a")])
    ]
  
hunit_linearizeList_test = -- TODO
  -- The 'linearizeList' functions concatenates a token list to a string
  -- linearizeList :: Bool -> [LinToken] -> String
  TestList [
  ]

hunit_getNewTrees_test = -- TODO
  -- The 'getNewTrees' function generates a set of related trees given a MetaTTree and a position in a token list 
  -- getNewTrees :: Grammar -> [LinToken] -> MetaTTree -> Pos -> S.Set MetaTTree
  TestList [
  ]

hunit_treesToStrings_test = -- TODO
  -- The 'treesToStrings' generates a list of strings based on the differences in similar trees
  -- treesToStrings :: Grammar -> Language -> S.Set MetaTTree -> S.Set String
  TestList [
  ]
  
hunit_getSuggestions_test = -- TODO
-- The 'getSuggestions' function generates a list of similar trees given a tree and a position in the token list
-- getSuggestions :: Grammar -> Language -> [LinToken] -> MetaTTree -> Pos -> S.Set String
  TestList [
  ]
  
linearize_tests = TestList [
  TestLabel "linearizeTree" hunit_linearizeTree_test,
  TestLabel "linearizeList" hunit_linearizeList_test
  ]

suggestion_tests =
  TestList [
  TestLabel "getNewTrees" hunit_getNewTrees_test,
  TestLabel "treesToStrings" hunit_treesToStrings_test,
  TestLabel "getSuggestions" hunit_getSuggestions_test
  ]

hunit_tests = TestList [linearize_tests, suggestion_tests]
