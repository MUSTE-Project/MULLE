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

hunit_updateClick_test =
  -- -- | The function 'updateClick' either increases the counter when the position is the same as the previous one or sets the new position and sets the counter to 1
  -- updateClick :: Maybe Click -> Pos -> Maybe Click
  let
    click1 = Nothing
    click2 = Just $ Click 0 0
    click3 = Just $ Click 2 2
  in
    TestList [
    TestLabel "Nothing" ( updateClick click1 0 ~?= ( Just $ Click 0 1 ) ),
    TestLabel "Just Click same position 1" ( updateClick click2 0 ~?= ( Just $ Click 0 1 ) ) ,
    TestLabel "Just Click same position 2" ( updateClick click3 2 ~?= ( Just $ Click 2 3 ) ) ,
    TestLabel "Just Click different position" ( updateClick click3 0 ~?= ( Just $ Click 0 1 ) )
    ]
  
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
  
hunit_linearizeList_test = 
  -- The 'linearizeList' functions concatenates a token list to a string
  -- linearizeList :: Bool -> [LinToken] -> String
  let
    list1 = []
    list2 = [([0],"a")]
    list3 = [([0,0],"a"),([0],"x"),([0,1],"b")]
  in
    TestList [
    TestLabel "Empty List without Path" ( linearizeList False False list1 ~?= "" ),
    TestLabel "Empty List with Path" ( linearizeList True False list1 ~?= "  []" ),
    TestLabel "One Element without Path" ( linearizeList False False list2 ~?= "a" ),
    TestLabel "One Element with Path" ( linearizeList True False list2 ~?= "  [0] a [0]   []" ),
    TestLabel "Simple List without Path" ( linearizeList False False list3 ~?= "a x b" ),
    TestLabel "Simple List with Path" ( linearizeList True False list3 ~?= "  [0,0] a [0,0]   [0] x [0]   [0,1] b [0,1]   []" ),
    TestLabel "Empty List without Path and Positions" ( linearizeList False True list1 ~?= "(0)  " ),
    TestLabel "Empty List with Path and Positions" ( linearizeList True True list1 ~?= "(0)   []" ),
    TestLabel "One Element without Path and Positions" ( linearizeList False True list2 ~?= "(0)   (1) a (2)  " ),
    TestLabel "One Element with Path and Positions" ( linearizeList True True list2 ~?= "(0)   [0] (1) a [0] (2)   []" ),
    TestLabel "Simple List without Path and Positions" ( linearizeList False True list3 ~?= "(0)   (1) a (2)   (3) x (4)   (5) b (6)  " ),
    TestLabel "Simple List with Path and Positions" ( linearizeList True True list3 ~?= "(0)   [0,0] (1) a [0,0] (2)   [0] (3) x [0] (4)   [0,1] (5) b [0,1] (6)   []" )
  ]

hunit_getNewTreeSet_test = -- TODO
  -- | The 'getNewTrees' function generates a set of related trees given a MetaTTree and a path
  -- getNewTrees :: Grammar -> MetaTTree -> Path -> S.Set MetaTTree
  let
    pgfFile = readPGF "gf/ABCAbs.pgf"
    grammar = fmap pgfToGrammar pgfFile
--    tree1 is in Test.Data
    path1 = []
    tree2 = TNode "a" (Fun "A" []) []
  in
    TestList [
    TestLabel "Tree 2" (TestCase $ grammar >>= (\g -> getNewTreesSet g (head $ languages $ pgf g) tree1 path1 3 @?= empty) )
    ]
    
hunit_treesToStrings_test = -- TODO
  -- The 'treesToStrings' generates a list of strings based on the differences in similar trees
  -- treesToStrings :: Grammar -> Language -> [TTree] -> [String]
  let
    pgfFile = readPGF "gf/ABCAbs.pgf"
    grammar = fmap pgfToGrammar pgfFile
    tree2 = TNode "a" (Fun "A" []) []
  in
    TestList [
    TestLabel "Empty tree list" (TestCase $ grammar >>= (\g -> treesToStrings g (head $ languages $ pgf g) [] @?= []) ),
    TestLabel "Meta tree in tree list" (TestCase $ grammar >>= (\g -> treesToStrings g (head $ languages $ pgf g) [tree1] @?= ["?0"]) ),
    TestLabel "Two trees in tree list 1" (TestCase $ grammar >>= (\g -> treesToStrings g (head $ languages $ pgf g) [tree1,tree2] @?= ["?0","a"]) ),
    TestLabel "Two trees in tree list 2" (TestCase $ grammar >>= (\g -> treesToStrings g (head $ languages $ pgf g) [tree2,tree1] @?= ["a","?0"]) ),
    TestLabel "Empty Grammar" (treesToStrings emptyGrammar (mkCId "ABC1") [tree2,tree1] ~?= ["?0","?0"]) -- Maybe strange result
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

prop_updateClick :: Maybe Click -> Pos -> Bool
prop_updateClick click pos =
  isJust $ updateClick click pos
  
various_tests = TestList [
  TestLabel "updateClick" hunit_updateClick_test,
  TestLabel "preAndSuffix" hunit_preAndSuffix_test
  ]
  
linearize_tests = TestList [
  TestLabel "linearizeTree" hunit_linearizeTree_test,
  TestLabel "linearizeList" hunit_linearizeList_test -- This test fails at the moment
  ]

suggestion_tests =
  TestList [
  -- TestLabel "getNewTrees" hunit_getNewTrees_test, -- This test takes too long at the moment
  TestLabel "treesToStrings" hunit_treesToStrings_test,
  TestLabel "getSuggestions" hunit_getSuggestions_test
  ]

hunit_tests = TestList [various_tests,linearize_tests, suggestion_tests]

quickcheck_tests :: [(TestName,Property)]
quickcheck_tests = [
  ("Updated clicks are never Nothing",property prop_updateClick)
  ]
