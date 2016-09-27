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
    tree1 = MetaTTree (read "{?A}") $ fromList [([],read "{a:A}")]
    tree2 = MetaTTree (read "{a:A}") $ empty
  in
    TestList [
    TestLabel "Grammar without a name" $ TestCase $ grammar >>= (\g -> linearizeTree g (mkCId "ABC1") tree1 @?= []),
    TestLabel "Grammar without a name" $ TestCase $ grammar >>= (\g -> linearizeTree g (mkCId "ABC1") tree2 @?= []),
    TestLabel "Grammar without a name" $ TestCase $ (1 @?= 2) -- grammar >>= (\g -> linearizeTree g (mkCId "ABC1") tree2 @?= [])
    ]
  
hunit_linearizeList_test =
  -- The 'linearizeList' functions concatenates a token list to a string
  -- linearizeList :: Bool -> [LinToken] -> String
  TestList [
  ]

hunit_getNewTrees_test =
  -- The 'getNewTrees' function generates a set of related trees given a MetaTTree and a position in a token list 
  -- getNewTrees :: Grammar -> [LinToken] -> MetaTTree -> Pos -> S.Set MetaTTree
  TestList [
  ]

hunit_treesToStrings_test =
  -- The 'treesToStrings' generates a list of strings based on the differences in similar trees
  -- treesToStrings :: Grammar -> Language -> S.Set MetaTTree -> S.Set String
  TestList [
  ]
  
hunit_getSuggestions_test = 
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
