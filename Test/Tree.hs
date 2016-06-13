{- | Implements several tests to control the validy of the program
-}
module Test.Tree where
import Test.QuickCheck
import PGF hiding (checkType)
import PGF.Internal
import Muste.Tree.Internal
import Muste.Grammar.Internal
import Test.HUnit.Text
import Test.HUnit.Base
import System.Random
import Data.Set (Set,fromList,toList,empty)
import Data.Maybe
import Test.Data (grammar)

randomize :: StdGen -> [a] -> [a]
randomize _ [] = []
randomize gen list =
  let
    (rnd, ngen) = randomR (0,length list - 1) gen
    (part1,_:part2) = splitAt rnd list
  in
    (list !! rnd) : (randomize ngen (part1 ++ part2))

-- HUnit tests
hunit_TreeC_GFAbsTree_showTree_test =
  let
    tree = (EApp (EFun (mkCId "A")) (EFun (mkCId "B")))
  in
    TestList [
    TestLabel "Single example" $ ( showTree tree ~=? "EApp (EFun A) (EFun B)" )
    ]

hunit_TreeC_GFAbsTree_selectNode_test =
  let
    tree = (EApp (EApp (EApp (EFun (mkCId "1")) (EApp (EFun (mkCId "2")) (EFun (mkCId "3")))) (EFun (mkCId "4"))) (EFun (mkCId "5")))
  in
    TestList [
    ( TestLabel "Existing Path 1" $ selectNode tree [0,0,0] ~?= Just (EFun (mkCId "1")) ),
    ( TestLabel "Existing Path 2" $ selectNode tree [0,0,1,0] ~?= Just (EFun (mkCId "2")) ),
    ( TestLabel "Path too deep" $ selectNode tree [0,0,0,0] ~?= Nothing ),
    ( TestLabel "Branch out of range" $ selectNode tree [0,2] ~?= Nothing ), 
    ( TestLabel "Negative Branch" $ selectNode tree [-1] ~?= Nothing )
    ]

hunit_TreeC_GFAbsTree_selectBranch_test =
  let
    tree = (EApp (EFun (mkCId "1")) (EFun (mkCId "2")))
  in
    TestList [
    ( TestLabel "Existing Branch 1" $ selectBranch tree 0 ~?= Just (EFun (mkCId "1")) ),
    ( TestLabel "Existing Branch 2" $ selectBranch tree 1 ~?= Just (EFun (mkCId "2")) ),
    ( TestLabel "Negative Branch" $ selectBranch tree (-1) ~?= Nothing ),
    ( TestLabel "Branch out of range" $ selectBranch tree 2 ~?= Nothing )
    ]
    
hunit_TreeC_TTree_showTree_test =
  let
    tree1 = TMeta (mkCId "A")
    tree2 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"), (mkCId "B")])
      [
       TMeta (mkCId "A"),
       TMeta (mkCId "B")
      ]
    tree3 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"), (mkCId "B")])
      [
        TNode (mkCId "a") (Fun (mkCId "A") []) [],
        TNode (mkCId "b") (Fun (mkCId "B") []) []
      ]
  in
    TestList [
    ( TestLabel "Meta tree" $ showTree tree1 ~?= "{?A}" ),
    ( TestLabel "Simple tree with metas" $ showTree tree2 ~?= "{f:(A -> B -> A) {?A} {?B}}" ),
    ( TestLabel "Simple tree" $ showTree tree3 ~?= "{f:(A -> B -> A) {a:(A)} {b:(B)}}" )
    ]

hunit_TreeC_TTree_selectNode_test =
  let
    tree = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"), (mkCId "B")])
      [
        TNode (mkCId "a") (Fun (mkCId "A") []) [],
        TNode (mkCId "g") (Fun (mkCId "B") [(mkCId "B"), (mkCId "C")])
        [
          TNode (mkCId "b") (Fun (mkCId "B") []) [],
          TNode (mkCId "c") (Fun (mkCId "C") []) []
        ]
      ]
  in
    TestList [
    ( TestLabel "Existing Path" $ selectNode tree [1,0] ~?= Just ( TNode (mkCId "b") (Fun (mkCId "B") []) [] ) ),
    ( TestLabel "Path too deep" $ selectNode tree [1,1,1] ~?= Nothing ),
    ( TestLabel "Branch out of range" $ selectNode tree [0,2] ~?= Nothing ), 
    ( TestLabel "Negative Branch" $ selectNode tree [-1] ~?= Nothing )
    ]

hunit_TreeC_TTree_selectBranch_test =
  let
    tree = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"), (mkCId "B")])
      [
        TNode (mkCId "a") (Fun (mkCId "A") []) [],
        TNode (mkCId "b") (Fun (mkCId "B") []) [],
        TNode (mkCId "c") (Fun (mkCId "C") []) []
      ]
  in
    TestList [
    ( TestLabel "Existing Branch 1" $ selectBranch tree 0 ~?= Just (TNode (mkCId "a") (Fun (mkCId "A") []) []) ),
    ( TestLabel "Existing Branch 2" $ selectBranch tree 1 ~?= Just (TNode (mkCId "b") (Fun (mkCId "B") []) []) ),
    ( TestLabel "Existing Branch 2" $ selectBranch tree 2 ~?= Just (TNode (mkCId "c") (Fun (mkCId "C") []) []) ),
    ( TestLabel "Negative Branch" $ selectBranch tree (-1) ~?= Nothing ),
    ( TestLabel "Branch out of range" $ selectBranch tree 3 ~?= Nothing )
    ]

hunit_consumeChar_test =
  let
    empty = ""
    match = " 12345"
    matched = "12345"
    nonmatch = "_12345"
  in
    TestList [
    ( TestLabel "Empty String" $ consumeChar ' ' empty ~?= empty ),
    ( TestLabel "Matching String" $ consumeChar ' ' match ~?= matched ),
    ( TestLabel "Non-Matching String" $ consumeChar ' ' nonmatch ~?= nonmatch )
    ]

hunit_readFunType_test =
  -- let
  --   type1 = "A"
  --   type2  = "(A)"
  --   type3 = "(A -> B)"
  --   type4 = "(A -> B -> A)"
  --   type5 = "A -> B"
  --   type6 = "(A->B)"
  --   type7 = "A->B"
  -- in
  --   TestList [
  --   ( TestLabel "Simple Type 1" $ readFunType type1 ~?= Just ((Fun (mkCId "A") []), "") ),
  --   ( TestLabel "Simple Type 2" $ readFunType type2 ~?= Just ((Fun (mkCId "A") []), "") ),
  --   ( TestLabel "Function Type 1" $ readFunType type3 ~?= Just ((Fun (mkCId "B") [(mkCId "A")]), "") ),
  --   ( TestLabel "Function Type 2" $ readFunType type4 ~?= Just ((Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]), "") ),
  --   ( TestLabel "Simple Type with rest 1" $ readFunType ( type1 ++ "###" ) ~?= Just ((Fun (mkCId "A") []), "###") ),
  --   ( TestLabel "Simple Type with rest 2" $ readFunType ( type2 ++ "###" )~?= Just ((Fun (mkCId "A") []), "###") ),
  --   ( TestLabel "Function Type with rest 1" $ readFunType ( type3 ++ "###" ) ~?= Just ((Fun (mkCId "B") [(mkCId "A")]), "###") ),
  --   ( TestLabel "Function Type with rest 2" $ readFunType ( type4 ++ "###" ) ~?= Just ((Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]), "###") ),
  --   ( TestLabel "Function Type without parentheses" $ readFunType type5 ~?= Just ((Fun (mkCId "B") [(mkCId "A")]), "") ),
  --   ( TestLabel "Function Type without parentheses with rest" $ readFunType ( type5 ++ "###" ) ~?= Just ((Fun (mkCId "B") [(mkCId "A")]), "###") ),
  --   ( TestLabel "Function Type without spaces" $ readFunType type6 ~?= Just ((Fun (mkCId "B") [(mkCId "A")]), "") ),
  --   ( TestLabel "Function Type without parentheses with rest" $ readFunType ( type6 ++ "###" ) ~?= Just ((Fun (mkCId "B") [(mkCId "A")]), "###") )
  --   ]
  TestCase $ assertString "Has to be checked in Grammar"

hunit_getChildCats_test =
  let
    tree1 = TMeta (mkCId "A")
    tree2 = TNode (mkCId "a") (Fun (mkCId "A") []) []
    tree3 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TMeta (mkCId "A")),(TMeta (mkCId "B"))]
    tree4 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TNode (mkCId "a") (Fun (mkCId "A") []) []) ,(TNode (mkCId "b") (Fun (mkCId "B") []) [])]
  in
    TestList [
    ( TestLabel "Meta node" $ getChildCats tree1 ~?= [] ),
    ( TestLabel "Simple tree without subtrees" $ getChildCats tree2 ~?= [] ),
    ( TestLabel "Simple tree with meta nodes" $ getChildCats tree3 ~?= [(mkCId "A"),(mkCId "B")] ),
    ( TestLabel "Simple tree with nodes" $ getChildCats tree4 ~?= [(mkCId "A"),(mkCId "B")] )
    ]

hunit_checkType_test =
  let
    tree1 = TMeta (mkCId "A")
    tree2 = TNode (mkCId "a") (Fun (mkCId "A") []) []
    tree3 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TMeta (mkCId "A")),(TMeta (mkCId "B"))]
    tree4 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TNode (mkCId "a") (Fun (mkCId "A") []) []) ,(TNode (mkCId "b") (Fun (mkCId "B") []) [])]
    tree5 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TMeta (mkCId "C")),(TMeta (mkCId "B"))]
    tree6 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TNode (mkCId "a") (Fun (mkCId "C") []) []) ,(TNode (mkCId "b") (Fun (mkCId "B") []) [])]
    tree7 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TMeta (mkCId "A")),(TMeta (mkCId "C"))]),(TMeta (mkCId "B"))]),(TMeta (mkCId "B"))]),(TMeta (mkCId "B"))]
  in
    TestList [
    ( TestLabel "Meta node" $ checkType tree1 ~?= True ),
    ( TestLabel "Simple tree without subtrees" $ checkType tree2 ~?= True ),
    ( TestLabel "Simple tree with meta nodes" $ checkType tree3 ~?= True ),
    ( TestLabel "Simple tree with nodes" $ checkType tree4 ~?= True ),
    ( TestLabel "Simple tree with meta nodes" $ checkType tree5 ~?= False ),
    ( TestLabel "Simple tree with nodes" $ checkType tree6 ~?= False ),
    ( TestLabel "Deep tree with nodes" $ checkType tree7 ~?= False )
    ]

hunit_fixTypes_test =
  let
    tree1 = TNode (mkCId "f") (Fun (mkCId "A") []) [(TMeta (mkCId "A")),(TMeta (mkCId "B"))]
    tree2 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TMeta (mkCId "A")),(TMeta (mkCId "B"))]
    tree3 = TNode (mkCId "f") (Fun (mkCId "A") []) [(TNode (mkCId "f") (Fun (mkCId "A") []) [(TNode (mkCId "f") (Fun (mkCId "A") []) [(TNode (mkCId "f") (Fun (mkCId "A") []) [(TMeta (mkCId "A"))])])])]
    tree4 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A")]) [(TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A")]) [(TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A")]) [(TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A")]) [(TMeta (mkCId "A"))])])])]
    tree5 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "C")]) [(TMeta (mkCId "A")),(TMeta (mkCId "B"))]
  in
    TestList [
    ( TestLabel "Fixable tree" $ fixTypes tree1 ~?= tree2 ),
    ( TestLabel "Already fixed tree" $ fixTypes tree2 ~?= tree2 ),
    ( TestLabel "Deep tree" $ fixTypes tree3 ~?= tree4 ),
    ( TestCase $ assertBool "Already fixed tree with type errors" $ fixTypes tree5 /= tree2 && fixTypes tree5 == tree5 )
    ]
    
treec_tests = TestList [
  TestLabel "TreeC GFAbsTree showTree" hunit_TreeC_GFAbsTree_showTree_test,
  TestLabel "TreeC GFAbsTree selectNode" hunit_TreeC_GFAbsTree_selectNode_test,
  TestLabel "TreeC GFAbsTree selectBranch" hunit_TreeC_GFAbsTree_selectBranch_test,
  TestLabel "TreeC TTree showTree" hunit_TreeC_TTree_showTree_test,
  TestLabel "TreeC TTree selectNode" hunit_TreeC_TTree_selectNode_test,
  TestLabel "TreeC TTree selectBranch" hunit_TreeC_TTree_selectBranch_test
  ]
  
tree_function_tests =
  TestList [
  TestLabel "consumeChar" hunit_consumeChar_test,
  TestLabel "readFunType" hunit_readFunType_test,
  TestLabel "getChildCats" hunit_getChildCats_test,
  TestLabel "checkType" hunit_checkType_test,
  TestLabel "fixTypes" hunit_fixTypes_test
  ]
  
hunit_tests = TestList [treec_tests, tree_function_tests]
    
-- Quickcheck tests
instance Arbitrary TTree where
  arbitrary =
    do
      let generated = toList $ Muste.Tree.Internal.generate grammar (mkCId "A") 3
      elements (map metaTree generated)

-- Just an example how to integrate quickcheck
prop_metaTest :: TTree -> Bool
prop_metaTest tree =
  (getMetaLeaves tree) == fromList (map snd (getMetaPaths tree))

 quickcheck_tests = [ ("Meta1",prop_metaTest) ]

