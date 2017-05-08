{-
   | Implements several tests to control the validy of the program
-}
module Test.Tree where
import Test.QuickCheck
import Test.Framework
import PGF hiding (checkType)
import PGF.Internal
import Muste.Tree.Internal
import Muste.Grammar.Internal
import Test.HUnit.Text
import Test.HUnit.Base hiding (Testable)
import System.Random
import Data.Set (Set,fromList,toList,empty,singleton)
import qualified Data.Set as Set
import Data.Maybe
-- Only needed for arbitrary trees at the moment
import Test.Data (grammar,tree1,tree2)

randomize :: StdGen -> [a] -> [a]
randomize _ [] = []
randomize gen list =
  let
    (rnd, ngen) = randomR (0,length list - 1) gen
    (part1,_:part2) = splitAt rnd list
  in
    (list !! rnd) : randomize ngen (part1 ++ part2)

-- HUnit tests
hunit_TreeC_GFAbsTree_showTree_test =
  let
    tree = EApp (EFun (mkCId "A")) (EFun (mkCId "B"))
  in
    TestList [
    TestLabel "Single example" ( showTree tree ~?= "EApp (EFun A) (EFun B)" )
    ]

hunit_TreeC_GFAbsTree_selectNode_test =
  let
    tree = EApp (EApp (EApp (EFun (mkCId "1")) (EApp (EFun (mkCId "2")) (EFun (mkCId "3")))) (EFun (mkCId "4"))) (EFun (mkCId "5"))
  in
    TestList [
    TestLabel "Existing Path 1" ( selectNode tree [0,0,0] ~?= Just (EFun (mkCId "1")) ),
    TestLabel "Existing Path 2" ( selectNode tree [0,0,1,0] ~?= Just (EFun (mkCId "2")) ),
    TestLabel "Path too deep" ( selectNode tree [0,0,0,0] ~?= Nothing ),
    TestLabel "Branch out of range" ( selectNode tree [0,2] ~?= Nothing ), 
    TestLabel "Negative Branch" ( selectNode tree [-1] ~?= Nothing )
    ]

hunit_TreeC_GFAbsTree_selectBranch_test =
  let
    tree = EApp (EFun (mkCId "1")) (EFun (mkCId "2"))
  in
    TestList [
    TestLabel "Existing Branch 1" ( selectBranch tree 0 ~?= Just (EFun (mkCId "1")) ),
    TestLabel "Existing Branch 2" ( selectBranch tree 1 ~?= Just (EFun (mkCId "2")) ),
    TestLabel "Negative Branch" ( selectBranch tree (-1) ~?= Nothing ),
    TestLabel "Branch out of range" ( selectBranch tree 2 ~?= Nothing )
    ]
    
hunit_TreeC_TTree_showTree_test =
  let
    -- tree1 in Data.hs   
    tree2 = TNode "f" (Fun "A" ["A", "B"])
      [
       tree1,
       TMeta "B"
      ]
    tree3 = TNode "f" (Fun "A" ["A", "B"])
      [
        TNode "a" (Fun "A" []) [],
        TNode "b" (Fun "B" []) []
      ]
  in
    TestList [
    TestLabel "Meta tree" ( showTree tree1 ~?= "TMeta \"A\"" ),
    TestLabel "Simple tree with metas" ( showTree tree2 ~?= "TNode \"f\" (Fun \"A\" [\"A\",\"B\"]) [TMeta \"A\",TMeta \"B\"]" ),
    TestLabel "Simple tree" ( showTree tree3 ~?= "TNode \"f\" (Fun \"A\" [\"A\",\"B\"]) [TNode \"a\" (Fun \"A\" []) [],TNode \"b\" (Fun \"B\" []) []]" )
    ]

hunit_TreeC_TTree_selectNode_test =
  let
    tree = TNode "f" (Fun "A" ["A", "B"])
      [
        TNode "a" (Fun "A" []) [],
        TNode "g" (Fun "B" ["B", "C"])
        [
          TNode "b" (Fun "B" []) [],
          TNode "c" (Fun "C" []) []
        ]
      ]
  in
    TestList [
    TestLabel "Existing Path" ( selectNode tree [1,0] ~?= Just ( TNode "b" (Fun "B" []) [] ) ),
    TestLabel "Path too deep" ( selectNode tree [1,1,1] ~?= Nothing ),
    TestLabel "Branch out of range" ( selectNode tree [0,2] ~?= Nothing ),
    TestLabel "Negative Branch"( selectNode tree [-1] ~?= Nothing )
    ]

hunit_TreeC_TTree_selectBranch_test =
  let
    tree = TNode "f" (Fun "A" ["A", "B"])
      [
        TNode "a" (Fun "A" []) [],
        TNode "b" (Fun "B" []) [],
        TNode "c" (Fun "C" []) []
      ]
  in
    TestList [
    TestLabel "Existing Branch 1" ( selectBranch tree 0 ~?= Just (TNode "a" (Fun "A" []) []) ),
    TestLabel "Existing Branch 2" ( selectBranch tree 1 ~?= Just (TNode "b" (Fun "B" []) []) ),
    TestLabel "Existing Branch 2" ( selectBranch tree 2 ~?= Just (TNode "c" (Fun "C" []) []) ),
    TestLabel "Negative Branch" ( selectBranch tree (-1) ~?= Nothing ),
    TestLabel "Branch out of range" ( selectBranch tree 3 ~?= Nothing )
    ]

hunit_Show_TTree_show_test =
  let
    -- tree1 in Data.hs
    str1 = "TMeta \"A\""
    tree2 = TMeta wildCard
    str2 = "TMeta \"*empty*\""
    tree3 = TNode "a" NoType []
    str3 = "TNode \"a\" NoType []"
    tree4 = TNode "a" (Fun "A" []) []
    str4 = "TNode \"a\" (Fun \"A\" []) []"
    tree5 = TNode "f" (Fun "A" ["A","B"]) [tree1,TMeta "B"]
    str5 = "TNode \"f\" (Fun \"A\" [\"A\",\"B\"]) [TMeta \"A\",TMeta \"B\"]"
    tree6 = TNode "f" (Fun "A" ["A","B"]) [TNode "a" (Fun "A" []) [],TNode "b" (Fun "B" []) []]
    str6 = "TNode \"f\" (Fun \"A\" [\"A\",\"B\"]) [TNode \"a\" (Fun \"A\" []) [],TNode \"b\" (Fun \"B\" []) []]"
    tree7 = TNode "f" (Fun "A" ["B"]) [TNode "g" (Fun "B" ["A"]) [TNode "a" (Fun "A" []) []]]
    str7 = "TNode \"f\" (Fun \"A\" [\"B\"]) [TNode \"g\" (Fun \"B\" [\"A\"]) [TNode \"a\" (Fun \"A\" []) []]]"
  in
    TestList [
    TestLabel "Simple Meta" ( show tree1 ~?= str1 ),
    TestLabel "Wildcard Meta" ( show tree2 ~?= str2 ),
    TestLabel "Simple tree without type" ( show tree3 ~?= str3 ),
    TestLabel "Simple tree" ( show tree4 ~?= str4 ),
    TestLabel "More complex tree with metas" ( show tree5 ~?= str5 ),
    TestLabel "More complex tree" ( show tree6 ~?= str6 ),
    TestLabel "Deep Tree" ( show tree7 ~?= str7 )
    ]

-- To be removed
-- hunit_Show_MetaTTree_show_test =
--   let
--     tree1 = MetaTTree (TMeta (mkCId "A")) $ fromList [([0],TNode (mkCId "a") (Fun (mkCId "A") []) [])]
--     str1 = "({?A}, [([0],{a:(A)})])"
--     tree2 = MetaTTree (TNode (mkCId "f") (Fun (mkCId "A") [mkCId "A",mkCId "B"]) [TMeta (mkCId "A"),TMeta (mkCId "B")]) $
--       fromList [
--           ([0],TNode (mkCId "a") (Fun (mkCId "A") []) []),
--           ([1],TNode "b" (Fun (mkCId "B") []) [])
--           ]
--     str2 = "({f:(A -> B -> A) {?A} {?B}}, [([0],{a:(A)}) ([1],{b:(B)})])"
--     tree3 = MetaTTree (TNode (mkCId "f") (Fun (mkCId "A") [mkCId "B"]) [TNode "g" (Fun (mkCId "B") [mkCId "A"]) [TMeta(mkCId "A")]]) $
--       fromList [([0,0,0],TNode (mkCId "a") (Fun (mkCId "A") []) [])]
--     str3 = "({f:(B -> A) {g:(A -> B) {?A}}}, [([0,0,0],{a:(A)})])"
--   in
--     TestList [
--     TestLabel "Simple tree with one pruned branch" ( show tree1 ~?= str1 ),
--     TestLabel "Simple tree with two pruned branches" ( show tree2 ~?= str2 ),
--     TestLabel "Deep tree" ( show tree3 ~?= str3 )
--     ]

-- Not needed anymore?
-- hunit_consumeChar_test =
--   let
--     empty = ""
--     match = " 12345"
--     matched = "12345"
--     nonmatch = "_12345"
--   in
--     TestList [
--     TestLabel "Empty String" ( consumeChar ' ' empty ~?= empty ),
--     TestLabel "Matching String" ( consumeChar ' ' match ~?= matched ),
--     TestLabel "Non-Matching String" ( consumeChar ' ' nonmatch ~?= nonmatch )
--     ]

-- To be removed
-- hunit_readFunType_test =
--   let
--     str1 = "A"
--     str2 = "(A)"
--     type1 = Fun "A" []
--     str3 = "A->B"
--     str4 = "A -> B"
--     str5 = "(A->B)"
--     str6 = "(A -> B)"
--     str7 = "( A -> B )"
--     type2 = Fun "B" ["A"]
--     str8 = ""
--     str9 = "_"
--     str10 = "###"
--     str11 = "->"
--     str12 = "-> A"
--     str13 = "A ->"
--   in
--     TestList [
--     TestLabel "Simple Type 1" ( readFunType str1 ~?= Just (type1, "") ),
--     TestLabel "Simple Type 2" ( readFunType str2 ~?= Just (type1, "") ),
--     TestLabel "Simple Type with rest 1" ( readFunType ( str2 ++ "###" ) ~?= Just (type1, "###") ),
--     TestLabel "Simple Type with rest 2" ( readFunType ( str2 ++ "   ###" ) ~?= Just (type1, "   ###") ),
--     TestLabel "Function Type 1" ( readFunType str3 ~?= Just (type2, "") ),
--     TestLabel "Function Type 2" ( readFunType str4 ~?= Just (type2, "") ),
--     TestLabel "Function Type 3" ( readFunType str5 ~?= Just (type2, "") ),
--     TestLabel "Function Type 4" ( readFunType str6 ~?= Just (type2, "") ),
--     TestLabel "Function Type 5" ( readFunType str7 ~?= Just (type2, "") ),
--     TestLabel "Function Type with rest 1" ( readFunType ( str6 ++ "###" ) ~?= Just (type2, "###") ),
--     TestLabel "Function Type with rest 2" ( readFunType ( str6 ++ "   ###" ) ~?= Just (type2, "   ###") ),
--     TestLabel "Empty String" ( readFunType str8 ~?= Nothing ),
--     TestLabel "Wildcard" ( readFunType str9 ~?= Nothing ),
--     TestLabel "Three Hashes" ( readFunType str10 ~?= Nothing ),
--     TestLabel "Arrow" ( readFunType str11 ~?= Nothing ),
--     TestLabel "Arrow A" ( readFunType str12 ~?= Just (type1, "") ),
--     TestLabel "A Arrow" ( readFunType str13 ~?= Just (type1, "") )
--     ]

hunit_getChildCats_test =
  let
    -- tree1 in Data.hs
    -- tree2 in Data.hs
    tree3 = TNode "f" (Fun "A" ["A","B"]) [tree1,TMeta "B"]
    tree4 = TNode "f" (Fun "A" ["A","B"]) [TNode "a" (Fun "A" []) [] ,TNode "b" (Fun "B" []) []]
  in
    TestList [
    TestLabel "Meta node" ( getChildCats tree1 ~?= [] ),
    TestLabel "Simple tree without subtrees" ( getChildCats tree2 ~?= [] ),
    TestLabel "Simple tree with meta nodes" ( getChildCats tree3 ~?= ["A","B"] ),
    TestLabel "Simple tree with nodes" ( getChildCats tree4 ~?= ["A","B"] )
    ]

hunit_checkType_test =
  let
    -- tree1 in Data.hs
    -- tree2 in Data.hs
    tree3 = TNode "f" (Fun "A" ["A","B"]) [TMeta "A",TMeta "B"]
    tree4 = TNode "f" (Fun "A" ["A","B"]) [TNode "a" (Fun "A" []) [] ,TNode "b" (Fun "B" []) []]
    tree5 = TNode "f" (Fun "A" ["A","B"]) [TMeta "C",TMeta "B"]
    tree6 = TNode "f" (Fun "A" ["A","B"]) [TNode "a" (Fun "C" []) [] ,TNode "b" (Fun "B" []) []]
    tree7 = TNode "f" (Fun "A" ["A","B"]) [TNode "f" (Fun "A" ["A","B"]) [TNode "f" (Fun "A" ["A","B"]) [TNode "f" (Fun "A" ["A","B"]) [TMeta "A",TMeta "C"],TMeta "B"],TMeta "B"],TMeta "B"]
  in
    TestList [
    TestLabel "Meta node" ( checkType tree1 ~?= True ),
    TestLabel "Simple tree without subtrees" ( checkType tree2 ~?= True ),
    TestLabel "Simple tree with meta nodes" ( checkType tree3 ~?= True ),
    TestLabel "Simple tree with nodes" ( checkType tree4 ~?= True ),
    TestLabel "Simple tree with meta nodes" ( checkType tree5 ~?= False ),
    TestLabel "Simple tree with nodes" ( checkType tree6 ~?= False ),
    TestLabel "Deep tree with nodes" ( checkType tree7 ~?= False )
    ]

hunit_fixTypes_test =
  let
    tree1 = TNode "f" (Fun "A" []) [TMeta "A",TMeta "B"]
    tree2 = TNode "f" (Fun "A" ["A","B"]) [TMeta "A",TMeta "B"]
    tree3 = TNode "f" (Fun "A" []) [TNode "f" (Fun "A" []) [TNode "f" (Fun "A" []) [TNode "f" (Fun "A" []) [TMeta "A"]]]]
    tree4 = TNode "f" (Fun "A" ["A"]) [TNode "f" (Fun "A" ["A"]) [TNode "f" (Fun "A" ["A"]) [TNode "f" (Fun "A" ["A"]) [TMeta "A"]]]]
    tree5 = TNode "f" (Fun "A" ["A","C"]) [TMeta "A",TMeta "B"]
  in
    TestList [
    TestLabel "Fixable tree" ( fixTypes tree1 ~?= tree2 ),
    TestLabel "Already fixed tree" ( fixTypes tree2 ~?= tree2 ),
    TestLabel "Deep tree" ( fixTypes tree3 ~?= tree4 ),
    TestCase $ assertBool "Already fixed tree with type errors" ( fixTypes tree5 /= tree2 && fixTypes tree5 == tree5 )
    ]

-- To be fixed
-- hunit_readTree_test =
--   let
--     str1 = ""
--     str2 = "{}"
--     str3 = "_"
--     str4 = "?"
--     str5 = "###"
--     str6 = "{a:A}"
--     tree1 = TNode "a" (Fun "A" []) []
--     str7 = "{a:A"
--     str8 = "a:A}"
--     str9 = "a:A"
--     str10 = "{f:(A -> B -> A) {a:A} {b:B}}"
--     tree2 = TNode "f" (Fun "A" ["A","B"])
--       [
--         TNode "a" (Fun "A" []) [],
--         TNode "b" (Fun "B" []) []
--       ]
--     str11 = "{f:(A -> A) {f:(A -> A) {f:(A -> A) {f:(A -> A) {a:A}}}}}"
--     tree3 = TNode "f" (Fun "A" ["A"])
--       [
--         TNode "f" (Fun "A" ["A"])
--         [
--           TNode "f" (Fun "A" ["A"])
--           [
--             TNode "f" (Fun "A" ["A"])
--             [
--               TNode "a" (Fun "A" []) []
--             ]
--           ]
--         ]
--       ]
--     str12 = "?A"
--     str13 = "{?A}"
--     tree4 = TMeta "A"
--     str14 = "{f:(A -> B -> A) {?A} {?B}}"
--     tree5 = TNode "f" (Fun "A" ["A","B"])
--       [
--         TMeta "A",
--         TMeta "B"
--       ]
--   in
--     TestList [
--     TestLabel "Empty String" ( readTree str1 ~?= Nothing ),
--     TestLabel "Curly Brackets" ( readTree str2 ~?= Nothing ),
--     TestLabel "Wildcard" ( readTree str3 ~?= Nothing ),
--     TestLabel "Questionmark" ( readTree str4 ~?= Nothing ),
--     TestLabel "Three Hashes" ( readTree str5 ~?= Nothing ),
--     TestLabel "Simple Tree" ( readTree str6 ~?= Just (tree1,"") ),
--     TestLabel "Partial Simple Tree 1" ( readTree str7 ~?= Just (tree1,"") ),
--     TestLabel "Partial Simple Tree 2" ( readTree str8 ~?= Just (tree1,"") ),
--     TestLabel "Partial Simple Tree 3" ( readTree str9 ~?= Just (tree1,"") ),
--     TestLabel "Slightly more complex Tree" ( readTree str10 ~?= Just (tree2,"") ),
--     TestLabel "Slightly more complex Tree" ( readTree str11 ~?= Just (tree3,"") ),
--     TestLabel "Simple Meta Tree 1" ( readTree str12 ~?= Just (tree4,"") ),
--     TestLabel "Simple Meta Tree 2" ( readTree str13 ~?= Just (tree4,"") ),
--     TestLabel "More complex Meta Tree" ( readTree str14 ~?= Just (tree5,"") ),
--     TestLabel "Simple Tree with rest" ( readTree (str7 ++ "###") ~?= Just (tree1,"###") ),
--     TestLabel "Simple Tree with rest" ( readTree (str7 ++ "   ###") ~?= Just (tree1,"###") ) -- Slightly unexpected
--     ]

-- To be fixed
-- hunit_readTrees_test =
--   let
--     str1 = ""
--     str2 = "{} {}"
--     str3 = "{a:A} {b:B}"
--     trees1 = [TNode "a" (Fun "A" []) [],TNode "b" (Fun "B" []) []]
--     str4 = "{f:(A -> B -> A) {a:A} {b:B}} {g:(B -> C -> B) {b:B} {c:C}}"
--     trees2 =
--       [
--         TNode "f" (Fun "A" ["A","B"])
--          [
--            TNode "a" (Fun "A" []) [],
--            TNode "b" (Fun "B" []) []
--          ],
--         TNode "g" (Fun "B" ["B","C"])
--          [
--            TNode "b" (Fun "B" []) [],
--            TNode "c" (Fun "C" []) []
--          ]
--       ]
--     str5 = "{a:A} {?B}"
--     trees3 =
--       [
--         TNode "a" (Fun "A" []) [],
--         TMeta "B"
--       ]
--     str6 = "{?A} {b:B}"
--     trees4 =
--         [
--         TMeta "A",
--         TNode "b" (Fun "B" []) []
--       ]
--   in
--     TestList [
--     TestLabel "Empty String" ( readTrees str1 ~?= ([],"") ),
--     TestLabel "Curly Brackets" ( readTrees str2 ~?= ([],"{} {}") ),
--     TestLabel "Simple Trees" ( readTrees str3 ~?= (trees1,"") ),
--     TestLabel "Slightly more complex Trees" ( readTrees str4 ~?= (trees2,"") ),
--     TestLabel "Some Metas 1" ( readTrees str5 ~?= (trees3,"") ),
--     TestLabel "Some Metas 2" ( readTrees str6 ~?= (trees4,"") ),
--     TestLabel "Some trees plus some rest" ( readTrees (str4 ++ "###") ~?= (trees2,"###") ),
--     TestLabel "Some trees plus some rest" ( readTrees (str4 ++ "   ###") ~?= (trees2,"   ###") )
--     ]

-- To be fixed
-- hunit_Read_TTree_readsPrec_test =
--   let
--     str1 = ""
--     str2 = "{}"
--     str3 = "_"
--     str4 = "?"
--     str5 = "###"
--     str6 = "{a:A}"
--     tree1 = TNode "a" (Fun "A" []) []
--     str7 = "{a:A"
--     str8 = "a:A}"
--     str9 = "a:A"
--     str10 = "{f:(A -> B -> A) {a:A} {b:B}}"
--     tree2 = TNode "f" (Fun "A" ["A","B"])
--       [
--         TNode "a" (Fun "A" []) [],
--         TNode "b" (Fun "B" []) []
--       ]
--     str11 = "{f:(A -> A) {f:(A -> A) {f:(A -> A) {f:(A -> A) {a:A}}}}}"
--     tree3 = TNode "f" (Fun "A" ["A"])
--       [
--         TNode "f" (Fun "A" ["A"])
--         [
--           TNode "f" (Fun "A" ["A"])
--           [
--             TNode "f" (Fun "A" ["A"])
--             [
--               TNode "a" (Fun "A" []) []
--             ]
--           ]
--         ]
--       ]
--     str12 = "?A"
--     str13 = "{?A}"
--     tree4 = TMeta "A"
--     str14 = "{f:(A -> B -> A) {?A} {?B}}"
--     tree5 = TNode "f" (Fun "A" ["A","B"])
--       [
--         TMeta "A",
--         TMeta "B"
--       ]
--   in
--     TestList [
--     TestLabel "Empty String" ( (reads str1 :: [(TTree,String)])~?= [] ),
--     TestLabel "Curly Brackets" ( (reads str2 :: [(TTree,String)])~?= [] ),
--     TestLabel "Wildcard" ( (reads str3 :: [(TTree,String)])~?= [] ),
--     TestLabel "Questionmark" ( (reads str3 :: [(TTree,String)])~?= [] ),
--     TestLabel "Three hashes" ( (reads str5 :: [(TTree,String)])~?= [] ),
--     TestLabel "Simple Tree" ( reads str6 ~?= [(tree1,"")] ),
--     TestLabel "Partial Simple Tree 1" ( reads str7 ~?= [(tree1,"")] ),
--     TestLabel "Partial Simple Tree 2" ( reads str8 ~?= [(tree1,"")] ),
--     TestLabel "Partial Simple Tree 3" ( reads str9 ~?= [(tree1,"")] ),
--     TestLabel "More complex Tree" ( reads str10 ~?= [(tree2,"")] ),
--     TestLabel "Complex Tree" ( reads str11 ~?= [(tree3,"")] ),
--     TestLabel "Meta Tree 1" ( reads str12 ~?= [(tree4,"")] ),
--     TestLabel "Meta Tree 2" ( reads str13 ~?= [(tree4,"")] ),
--     TestLabel "More complex Meta Tree" ( reads str14 ~?= [(tree5,"")] ),
--     TestLabel "More complex Tree plus Extra 1" ( reads (str10 ++ "###") ~?= [(tree2,"###")] ),
--     TestLabel "More complex Tree plus Extra 2" ( reads (str10 ++ "   ###") ~?= [(tree2,"   ###")] )
--     ]

hunit_listReplace_test = 
   let
     list1 = []
     list2 = ['a','a','b']
     list3 = ['a','a','a']
   in
     TestList [
     TestLabel "Empty List Positive Index" ( listReplace list1 2 'a' ~?= list1 ),
     TestLabel "Empty List Negative Index" ( listReplace list1 (-2) 'a' ~?= list1 ),
     TestLabel "Simple List Valid Index" ( listReplace list2 2 'a' ~?= list3 ),
     TestLabel "Simple List Negative Index" ( listReplace list2 (-2) 'a' ~?= list2 ),
     TestLabel "Simple List Index out of range" ( listReplace list2 3 'a' ~?= list2 )
     ]
     
hunit_powerList_test = 
  let
    list1 = [] :: [Int]
    list2 = [[]] :: [[Int]]
    list3 = [1]
    list4 = [[],[1]]
    list5 = ['a','b','c']
    list6 = [[],['c'],['b'],['b','c'],['a'],['a','c'],['a','b'],['a','b','c']]
  in
  TestList [
    TestLabel "Empty List" ( powerList list1 ~?= list2 ),
    TestLabel "One Element" ( powerList list3 ~?= list4 ),
    TestLabel "Three Elements" ( powerList list5 ~?= list6 )
    ]

hunit_isMeta_test =
  let
    -- tree1 in Data.hs
    tree2 = TMeta wildCard
    tree3 = TNode "a" NoType []
    tree4 = TNode "a" (Fun "A" []) []
    tree5 = TNode "f" (Fun "A" ["A","B"]) [TMeta "A",TMeta "B"]
  in
    TestList [
    TestLabel "Meta" ( isMeta tree1 ~?= True ),
    TestLabel "Meta with wildcard" ( isMeta tree2 ~?= True ),
    TestLabel "Simple Tree without type" ( isMeta tree3 ~?= False ),
    TestLabel "Simple tree" ( isMeta tree4 ~?= False ),
    TestLabel "Tree" ( isMeta tree5 ~?= False )
    ]

hunit_getTreeCat_test =
  let
    -- tree1 in Data.hs
    cat1 = "A"
    tree2 = TMeta wildCard
    cat2 = wildCard
    tree3 = TNode "a" NoType []
    cat3 = wildCard
    tree4 = TNode "f" (Fun "A" ["A","B"]) [TMeta "A",TMeta "B"]
  in
    TestList [
    TestLabel "Meta" ( getTreeCat tree1 ~?= cat1 ),
    TestLabel "Meta with wildcard" ( getTreeCat tree2 ~?= cat2 ),
    TestLabel "Simple Tree without type" ( getTreeCat tree3 ~?= cat3 ),
    TestLabel "Tree" ( getTreeCat tree4 ~?= cat1 )
    ]

hunit_gfAbsTreeToTTreeWithPGF_test =
  let
    pgf = readPGF "gf/ABCAbs.pgf"
    gtree1 = EFun (mkCId "a")
    ttree1 = TNode "a" (Fun "A" []) []
    gtree2 = EFun wildCId
    ttree2 = TNode "_" NoType []
    gtree3 = EApp (EApp (EFun (mkCId "f")) (EFun (mkCId "a"))) (EFun (mkCId "b"))
    ttree3 = TNode "f" (Fun "A" ["A","B"]) [TNode "a" (Fun "A" []) [],TNode "b" (Fun "B" []) []] -- read "{f:(A->B->A) {a:A} {b:B}}" :: TTree
    gtree4 = EApp (EApp (EFun (mkCId "f")) (EFun (mkCId "a"))) (EApp (EApp (EFun (mkCId "g")) (EFun (mkCId "b"))) (EFun (mkCId "c")))
    ttree4 = TNode "f" (Fun "A" ["A","B"]) [TNode "a" (Fun "A" []) [],TNode "g" (Fun "B" ["B","C"]) [TNode "b" (Fun "B" []) [], TNode "c" (Fun "C" []) []]] -- read "{f:(A->B->A) {a:A} {g:(B->C->B) {b:B} {c:C}}}" :: TTree
    gtree5 = ELit (LStr "Foo")
    ttree5 = TMeta wildCard
  in
    TestList [
    TestLabel "EFun" $ TestCase $ pgf >>= (\p -> gfAbsTreeToTTreeWithPGF p gtree1 @?= ttree1),
    TestLabel "EFun with wildcard" $ TestCase $ pgf >>= (\p -> gfAbsTreeToTTreeWithPGF p gtree2 @?= ttree2),
    TestLabel "EApp 1" $ TestCase $ pgf >>= (\p -> gfAbsTreeToTTreeWithPGF p gtree3 @?= ttree3),
    TestLabel "EApp 2" $ TestCase $ pgf >>= (\p -> gfAbsTreeToTTreeWithPGF p gtree4 @?= ttree4),
    TestLabel "ELit" $ TestCase $ pgf >>= (\p -> gfAbsTreeToTTreeWithPGF p gtree5 @?= ttree5)
    ]

hunit_gfAbsTreeToTTreeWithGrammar_test =
  let
    pgf = readPGF "gf/ABCAbs.pgf"
    grammar = fmap pgfToGrammar pgf
    gtree1 = EFun (mkCId "a")
    ttree1 = TNode "a" (Fun "A" []) []
    gtree2 = EFun wildCId
    ttree2 = TNode "_" NoType []
    gtree3 = EApp (EApp (EFun (mkCId "f")) (EFun (mkCId "a"))) (EFun (mkCId "b"))
    ttree3 = TNode "f" (Fun "A" ["A","B"]) [TNode "a" (Fun "A" []) [],TNode "b" (Fun "B" []) []] -- read "{f:(A->B->A) {a:A} {b:B}}" :: TTree
    gtree4 = EApp (EApp (EFun (mkCId "f")) (EFun (mkCId "a"))) (EApp (EApp (EFun (mkCId "g")) (EFun (mkCId "b"))) (EFun (mkCId "c")))
    ttree4 = TNode "f" (Fun "A" ["A","B"]) [TNode "a" (Fun "A" []) [],TNode "g" (Fun "B" ["B","C"]) [TNode "b" (Fun "B" []) [], TNode "c" (Fun "C" []) []]] -- read "{f:(A->B->A) {a:A} {g:(B->C->B) {b:B} {c:C}}}" :: TTree
    gtree5 = ELit (LStr "Foo")
    ttree5 = TMeta wildCard
  in
    TestList [
    TestLabel "EFun" $ TestCase $ grammar >>= (\g -> gfAbsTreeToTTreeWithGrammar g gtree1 @?= ttree1),
    TestLabel "EFun with wildcard" $ TestCase $ grammar >>= (\g -> gfAbsTreeToTTreeWithGrammar g gtree2 @?= ttree2),
    TestLabel "EApp 1" $ TestCase $ grammar >>= (\g -> gfAbsTreeToTTreeWithGrammar g gtree3 @?= ttree3),
    TestLabel "EApp 2" $ TestCase $ grammar >>= (\g -> gfAbsTreeToTTreeWithGrammar g gtree4 @?= ttree4),
    TestLabel "ELit" $ TestCase $ grammar >>= (\g -> gfAbsTreeToTTreeWithGrammar g gtree5 @?= ttree5)
    ]

hunit_ttreeToGFAbsTree_test = 
  let
    ttree1 = TNode "a" (Fun "A" []) [] -- read "{a:A}" :: TTree
    gtree1 = EFun (mkCId "a")
    ttree2 = TNode wildCard NoType []
    gtree2 = EFun wildCId
    ttree3 = TNode "f" (Fun "A" ["A","B"]) [TNode "a" (Fun "A" []) [], TNode "b" (Fun "B" []) []] -- read "{f:(A->B->A) {a:A} {b:B}}" :: TTree 
    gtree3 = EApp (EApp (EFun (mkCId "f")) (EFun (mkCId "a"))) (EFun (mkCId "b"))
    ttree4 = TNode "f" (Fun "A" ["A","B"]) [TNode "a" (Fun "A" []) [], TNode "g" (Fun "B" ["B","C"]) [TNode "b" (Fun "B" []) [],TNode "c" (Fun "C" []) []]] -- read "{f:(A->B->A) {a:A} {g:(B->C->B) {b:B} {c:C}}}"
    gtree4 = EApp (EApp (EFun (mkCId "f")) (EFun (mkCId "a"))) (EApp (EApp (EFun (mkCId "g")) (EFun (mkCId "b"))) (EFun (mkCId "c")))
    ttree5 = TMeta wildCard
    gtree5 = EMeta 0
    ttree6 = TNode "f" (Fun "A" ["A","B"]) [TMeta "A",TMeta "B"] -- read "{f:(A->B->A) {?A} {?B}}" :: TTree
    gtree6 = EApp (EApp (EFun (mkCId "f")) (EMeta 0)) (EMeta 1)
    ttree7 = TNode "h" (Fun "A" ["A","A","A"]) [TNode "a" (Fun "A" []) [], TNode "a" (Fun "A" []) [],TNode "a" (Fun "A" []) []] -- read "{h:(A->A->A->A) {a:A} {a:A} {a:A}}" :: TTree
    gtree7 = EApp (EApp (EApp (EFun (mkCId "h")) (EFun (mkCId "a"))) (EFun (mkCId "a"))) (EFun (mkCId "a"))
    ttree8 = TNode "h" (Fun "A" ["A","A","A"]) [TMeta "A", TNode "a" (Fun "A" []) [], TNode "f" (Fun "A" ["A","A"]) [TNode "a" (Fun "A" []) [], TMeta "A"]] -- read "{h:(A->A->A->A) {?A} {a:A} {f:(A->A->A) {a:A} {?A}}}" :: TTree
    gtree8 = EApp (EApp (EApp (EFun (mkCId "h")) (EMeta 0)) (EFun (mkCId "a"))) (EApp (EApp (EFun (mkCId "f")) (EFun (mkCId "a"))) (EMeta 1))
  in
    TestList [
    TestLabel "Simple Tree" ( ttreeToGFAbsTree ttree1 ~?= gtree1 ),
    TestLabel "Simple Tree with wildcard and without type" ( ttreeToGFAbsTree ttree2 ~?= gtree2 ),
    TestLabel "More complex Tree" ( ttreeToGFAbsTree ttree3 ~?= gtree3 ),
    TestLabel "More complex Tree" ( ttreeToGFAbsTree ttree4 ~?= gtree4 ),
    TestLabel "Meta" ( ttreeToGFAbsTree ttree5 ~?= gtree5 ),
    TestLabel "More Meta" ( ttreeToGFAbsTree ttree6 ~?= gtree6 ),
    TestLabel "More Children 1" ( ttreeToGFAbsTree ttree7 ~?= gtree7 ),
    TestLabel "More Children 2" ( ttreeToGFAbsTree ttree8 ~?= gtree8 )
    ]

hunit_ttreeToLTree_test =
  let
    ttree1 = TMeta "A"
    ltree1 = LNode (mkCId "A") 1 [LNode wildCId 0 [LLeaf]]
    ttree2 = TMeta "_"
    ltree2 = LNode wildCId 1 [LNode wildCId 0 [LLeaf]]
    ttree3 = TNode "a" (Fun "A" []) []
    ltree3 = LNode (mkCId "A") 0 []
    ttree4 = TNode "f" (Fun "A" ["A","B"])
      [
        TMeta "A",
        TMeta "B"
      ]
    ltree4 = LNode (mkCId "A") 4 [LNode (mkCId "A") 1 [LNode wildCId 0 [LLeaf]],LNode (mkCId "B") 3 [LNode wildCId 2 [LLeaf]]]
    ttree5 = TNode "f" (Fun "A" ["A","B"])
      [
        TNode "a" (Fun "A" []) [],
        TNode "b" (Fun "B" []) []
      ]
    ltree5 = LNode (mkCId "A") 2 [LNode (mkCId "A") 0 [],LNode (mkCId "B") 1 []]
  in
    TestList [
    TestLabel "Meta" ( ttreeToLTree ttree1 ~?= ltree1 ),
    TestLabel "Meta with wildcard" ( ttreeToLTree ttree2 ~?= ltree2 ),
    TestLabel "Simple Tree" ( ttreeToLTree ttree3 ~?= ltree3 ),
    TestLabel "Tree with Metas" ( ttreeToLTree ttree4 ~?= ltree4 ),
    TestLabel "Tree" ( ttreeToLTree ttree5 ~?= ltree5 )
    ]

hunit_showBracket_test = 
  let
    bracket1 = Leaf "foo";
    bracket2 = Bracket (mkCId "foo") 0 0 (mkCId "bar") [] [];
    bracket3 = Bracket (mkCId "foo") 0 0 (mkCId "bar") [EFun (mkCId "baz")] [Leaf "baz"];
  in
    TestList [
    TestLabel "Leaf" ( showBracket bracket1 ~?= "[Leaf (token:foo)]" ),
    TestLabel "Simple Bracket" ( showBracket bracket2 ~?= "[Bracket (cid1:foo) (fid:0) (lindex:0) (cid2:bar) (exprs:[]) (bs:[]) ]" ),
    TestLabel "Recursive Bracket" ( showBracket bracket3 ~?= "[Bracket (cid1:foo) (fid:0) (lindex:0) (cid2:bar) (exprs:[EFun baz]) (bs:[[Leaf (token:baz)]]) ]" )
    ]
  
hunit_getPath_test =
  let
    tree1 = ttreeToLTree $ TMeta "A" -- read "{?A}"
    tree2 = ttreeToLTree $ TNode "s" (Fun "S" ["A"]) [TNode "f" (Fun "A" ["A","B"]) [TMeta "A",TNode "b" (Fun "B" []) []]] -- read "{s:(A->S) {f:(A->B->A) {?A} {b:B}}}"
    tree3 = ttreeToLTree $ TNode "s" (Fun "S" ["A"]) [TNode "h" (Fun "A" ["A","A","A"]) [TMeta "A",TNode "a1" (Fun "A" []) [], TNode "a2" (Fun "A" []) [],TMeta "A"]] -- read "{s:(A->S) {h:(A->A->A->A) {?A} {a1:A} {a2:A} {?A}}}"
  in
    TestList [
    TestLabel "Meta Negative Id" ( getPath tree1 (-1) ~?= [] ),
    TestLabel "Meta Matching Id" ( getPath tree1 0 ~?= [0] ),
    TestLabel "Meta Id out of range" ( getPath tree1 1 ~?= [] ),
    TestLabel "Tree 1 Matching Id 1" ( getPath tree2 0 ~?= [0,0,0] ),
    TestLabel "Tree 1 Matching Id 2" ( getPath tree2 1 ~?= [0,0] ),
    TestLabel "Tree 1 Matching Id 3" ( getPath tree2 2 ~?= [0,1] ),
    TestLabel "Tree 2 Matching Id 1" ( getPath tree3 0 ~?= [0,0,0] ),
    TestLabel "Tree 2 Matching Id 2" ( getPath tree3 1 ~?= [0,0] ),
    TestLabel "Tree 2 Matching Id 3" ( getPath tree3 2 ~?= [0,1] ),
    TestLabel "Tree 2 Matching Id 4" ( getPath tree3 3 ~?= [0,2] ),
    TestLabel "Tree 2 Matching Id 5" ( getPath tree3 4 ~?= [0,3,0] ),
    TestLabel "Tree 2 Matching Id 6" ( getPath tree3 5 ~?= [0,3] ),
    TestLabel "Tree 2 Matching Id 7" ( getPath tree3 6 ~?= [0] ),
    TestLabel "Tree 2 Matching Id 8" ( getPath tree3 7 ~?= [] )
    ]
  
hunit_maxDepth_test =
  let
    -- tree1 in Data.hs
    tree2 = TMeta wildCard
    tree3 = TNode "a" NoType []
    tree4 = TNode "f" (Fun "E" ["A","B","C","D"])
      [
        TMeta "A",
        TNode "b" (Fun "B" []) [],
        TNode "g" (Fun "C" ["C","B"])
         [
           TNode "c" (Fun "C" []) [],
           TNode "h" (Fun "B" ["B"])
            [
              TNode "h" (Fun "B" ["B"])
               [
                 TNode "b" (Fun "B" []) []
               ]
            ]
         ],
        TNode "i" (Fun ("D") ["D"])
         [
           TNode "i" (Fun ("D") ["D"]) []
         ]
      ]
  in
    TestList [
    TestLabel "Meta" $ maxDepth tree1 ~?= 1,
    TestLabel "Meta with wildcard" $ maxDepth tree2 ~?= 1,
    TestLabel "Simple tree without type" $ maxDepth tree3 ~?= 1,
    TestLabel "Complex tree" $ maxDepth tree4 ~?= 5
    ]

hunit_countNodes_test =
  let
    -- tree1 in Data.hs
    tree2 = TMeta wildCard
    tree3 = TNode "a" NoType []
    tree4 = TNode "f" (Fun "E" ["A","B","C","D"])
      [
        TMeta "A",
        TNode "b" (Fun "B" []) [],
        TNode "g" (Fun "C" ["C","B"])
         [
           TNode "c" (Fun "C" []) [],
           TNode "h" (Fun "B" ["B"])
            [
              TNode "h" (Fun "B" ["B"])
               [
                 TNode "b" (Fun "B" []) []
               ]
            ]
         ],
        TNode "i" (Fun ("D") ["D"])
         [
           TNode "i" (Fun ("D") ["D"]) []
         ]
      ]
  in
    TestList [
    TestLabel "Meta" $ countNodes tree1 ~?= 0,
    TestLabel "Meta with wildcard" $ countNodes tree2 ~?= 0,
    TestLabel "Simple tree without type" $ countNodes tree3 ~?= 1,
    TestLabel "Complex tree" $ countNodes tree4 ~?= 9
             ]

-- To be removed
-- hunit_makeMeta_test =
--   let
--     -- tree1 in Data.hs
--     ttree1 = tree1
--     mtree1 = TTree tree1
--     ttree2 = TNode "a" (Fun "A" []) []
--     mtree2 = MetaTTree (TNode "a" (Fun "A" []) []) empty
--     in
--     TestList [
--     TestLabel "Meta" ( makeMeta ttree1 ~?= mtree1 ),
--     TestLabel "Simple Tree" ( makeMeta ttree2 ~?= mtree2 )
--     ]

hunit_replaceBranch_test = 
  let
    new = TMeta wildCard
    -- tree1 in Data.hs
    tree2 = TNode "f" NoType []
    tree3 = TNode "f" (Fun "A" ["A","B","C","D"])
      [
        TNode "a" (Fun "A" []) [],
        TMeta "B",
        TNode "g" (Fun "C" ["C"]) [TMeta "C"],
        TNode "d" (Fun ("D") []) []
      ]
  in
    TestList [
    TestLabel "Meta" ( replaceBranch tree1 0 new ~?= tree1 ),
    TestLabel "Meta negative index" ( replaceBranch tree1 (-1) new ~?= tree1 ),
    TestLabel "Meta index out of range" ( replaceBranch tree1 1 new ~?= tree1 ),
    TestLabel "Simple Tree without type" ( replaceBranch tree2 0 new ~?= tree2 ),
    TestLabel "Simple Tree without type and negative index" ( replaceBranch tree2 (-1) new ~?= tree2 ),
    TestLabel "Simple Tree without type and index out of range" ( replaceBranch tree2 1 new ~?= tree2 ),
    TestLabel "Tree" ( selectBranch (replaceBranch tree3 0 new) 0 ~?= Just new ),
    TestLabel "Tree" ( selectBranch (replaceBranch tree3 1 new) 1 ~?= Just new ),
    TestLabel "Tree" ( selectBranch (replaceBranch tree3 2 new) 2 ~?= Just new ),
    TestLabel "Tree" ( selectBranch (replaceBranch tree3 3 new) 3 ~?= Just new ),
    TestLabel "Tree negative index" ( replaceBranch tree3 (-1) new ~?= tree3 ),
    TestLabel "Tree index out of range" ( replaceBranch tree3 5 new ~?= tree3 )
    ]

hunit_replaceNode_test = 
  let
    new = TMeta wildCard
    -- tree1 in Data.hs
    tree2 = TNode "f" NoType []
    tree3 = TNode "f" (Fun "A" ["A","B","C","D"])
      [
        TNode "a" (Fun "A" []) [],
        TMeta "B",
        TNode "g" (Fun "C" ["C"]) [TMeta "C"],
        TNode "d" (Fun "D" []) []
      ]
  in
    TestList [
    TestLabel "Meta empty path" ( replaceNode tree1 [] new ~?= new ),
    TestLabel "Meta path too long" ( replaceNode tree1 [0] new ~?= tree1 ),
    TestLabel "Simple tree empty path" ( replaceNode tree2 [] new ~?= new ),
    TestLabel "Simple tree path too long" ( replaceNode tree2 [0] new ~?= tree2 ),
    TestLabel "Tree empty path" ( replaceNode tree3 [] new ~?= new ),
    TestLabel "Tree 1" ( selectNode (replaceNode tree3 [0] new) [0] ~?= Just new ),
    TestLabel "Tree 2" ( selectNode (replaceNode tree3 [1] new) [1] ~?= Just new ),
    TestLabel "Tree 3" ( selectNode (replaceNode tree3 [2] new) [2] ~?= Just new ),
    TestLabel "Tree 2" ( selectNode (replaceNode tree3 [2,0] new) [2,0] ~?= Just new ),
    TestLabel "Tree 2" ( selectNode (replaceNode tree3 [3] new) [3] ~?= Just new ),
    TestLabel "Tree negative path" ( replaceNode tree3 [-1] new ~?= tree3 ),
    TestLabel "Tree path out of range" ( replaceNode tree3 [4] new ~?= tree3 )
    
    ]

hunit_getMetaLeafCatsSet_test =
-- To be removed
-- hunit_replaceNodeByMeta_test = 
--   let
--     tree1 = MetaTTree (TMeta (mkCId "A")) empty
--     tree2 = MetaTTree (TMeta (mkCId "A")) $ fromList [([],TMeta (mkCId "A"))]
--     tree3 = MetaTTree (TNode "a" (Fun (mkCId "A") []) []) empty
--     tree4 = MetaTTree (TMeta (mkCId "A")) $ fromList [([],TNode "a" (Fun (mkCId "A") []) [])]
--     tree5 = MetaTTree (read "{f:(A->B->A) {a:A} {g:(B->C->B) {b:B} {?C}}}") $ fromList [([1,1],read "{c:C}")]
--     tree6 = MetaTTree (read "{f:(A->B->A) {?A} {g:(B->C->B) {b:B} {?C}}}") $ fromList [([0],read "{a:A}"),([1,1],read "{c:C}")]
--     tree7 = MetaTTree (read "{f:(A->B->A) {a:A} {?B}") $ fromList [([1],read "{g:(B->C->B) {b:B} {?C}}"),([1,1],read "{c:C}")]
--     tree8 = MetaTTree (read "{f:(A->B->A) {a:A} {g:(B->C->B) {?B} {?C}}}") $ fromList [([1,0],read "{b:B}"),([1,1],read "{c:C}")]
--   in
--     TestList [
--     TestLabel "Meta Tree with empty path 1" ( replaceNodeByMeta tree1 [] ~?= tree2 ),
--     TestLabel "Meta Tree with empty path 2" ( replaceNodeByMeta tree2 [] ~?= tree2 ),
--     TestLabel "Simple Tree with empty path" ( replaceNodeByMeta tree3 [] ~?= tree4 ),
--     TestLabel "Complex Tree with valid path 1" ( replaceNodeByMeta tree5 [0] ~?= tree6 ),
--     TestLabel "Complex Tree with valid path 2" ( replaceNodeByMeta tree5 [1] ~?= tree7 ),
--     TestLabel "Complex Tree with valid path 3" ( replaceNodeByMeta tree5 [1,0] ~?= tree8 ),
--     TestLabel "Complex Tree with invalid path 1" ( replaceNodeByMeta tree5 [-1] ~?= tree5 ),
--     TestLabel "Complex Tree with invalid path 2" ( replaceNodeByMeta tree5 [2] ~?= tree5 ),
--     TestLabel "Complex Tree with invalid path 3" ( replaceNodeByMeta tree5 [0,0] ~?= tree5 ),
--     TestLabel "Complex Tree with invalid path 4" ( replaceNodeByMeta tree5 [1,1,1] ~?= tree5 )
--     ]

hunit_maxPath_test =
  let
    -- tree1 in Data.hs
    -- tree2 in Data.hs
    tree3 = TNode "f" (Fun "A" ["A","B"])
      [
        tree1,
        TMeta wildCard
      ]
    tree4 = TNode "f" (Fun "A" ["A","A"])
      [
        tree1,
        tree1
      ]
    tree5 = TNode "f" (Fun "A" ["A","B"])
      [
        TNode "g" (Fun "A" ["A"])
        [
          TNode "g" (Fun "A" ["A"])
          [
            TNode "g" (Fun "A" ["A"])
            [
              tree1
            ]
          ]
        ],
        TMeta "B"
      ]
  in
    TestList [
    TestLabel "Meta" ( getMetaLeafCatsSet tree1 ~?= fromList ["A"] ),
    TestLabel "Simple tree without metas" ( getMetaLeafCatsSet tree2 ~?= empty ),
    TestLabel "Simple tree 1" ( getMetaLeafCatsSet tree3 ~?= fromList ["A",wildCard] ),
    TestLabel "Simple tree 2" ( getMetaLeafCatsSet tree4 ~?= fromList ["A"] ),
    TestLabel "Tree" ( getMetaLeafCatsSet tree5 ~?= fromList ["A","B"] )
    ]

-- To be removed
-- hunit_prune_test = 
--   let
--     tree1 = read "{f:(A -> B -> A) {a:A} {g:B {b:B} {c:C}}}" :: TTree
--     mtrees1 = fromList [
--       MetaTTree (read "{?A}") $ fromList [([], read "{f:(A -> B -> A) {a:A} {g:B {b:B} {c:C}}}")],
--       MetaTTree (read "{f:(A -> B -> A) {?A} {?B}}") $ fromList [([0], read "{a:A}"), ([1], read "{g:(B -> C -> B) {b:B} {c:C}}")],
--       MetaTTree (read "{f:(A -> B -> A) {a:A} {?B}}") $ fromList [([1], read "{g:(B -> C -> B) {b:B} {c:C}}")],
--       MetaTTree (read "{f:(A -> B -> A) {?A} {g:(B -> C -> B) {?B} {?C}}}") $ fromList [([0], read "{a:A}"), ([1,0], read "{b:B}"), ([1,1], read "{c:C}")],
--       MetaTTree (read "{f:(A -> B -> A) {?A} {g:(B -> C -> B) {b:B} {?C}}}") $ fromList [([0], read "{a:A}"), ([1,1], read "{c:C}")],
--       MetaTTree (read "{f:(A -> B -> A) {?A} {g:(B -> C -> B) {?B} {c:C}}}") $ fromList [([0], read "{a:A}"), ([1,0], read "{b:B}")],
--       MetaTTree (read "{f:(A -> B -> A) {?A} {g:(B -> C -> B) {b:B} {c:C}}}") $ fromList [([0], read "{a:A}")],
--       MetaTTree (read "{f:(A -> B -> A) {a:A} {g:(B -> C -> B) {?B} {?C}}}") $ fromList [([1,0], read "{b:B}"), ([1,1], read "{c:C}")],
--       MetaTTree (read "{f:(A -> B -> A) {a:A} {g:(B -> C -> B) {b:B} {?C}}}") $ fromList [([1,1], read "{c:C}")],
--       MetaTTree (read "{f:(A -> B -> A) {a:A} {g:(B -> C -> B) {?B} {c:C}}}") $ fromList [([1,0], read "{b:B}")],
--       MetaTTree (read "{f:(A -> B -> A) {a:A} {g:(B -> C -> B) {b:B} {c:C}}}") empty
--       ]
--   in
--     TestList [
--     -- prune {{f:A {a:A} {g:B {b:B} {c:C}}}} 2
--     -- [({?A}, [([], {{f:A {a:A} {g:B {b:B} {c:C}}}})]),
--     --  ({{f:A ?A ?B}}, [([0], {{a:A}}), ([1], {{g:B {b:B} {c:C}}})]),
--     --  ({{f:A {a:A} ?B}}, [([1], {{g:B {b:B} {c:C}}})]),
--     --  ({{f:A ?A {g:B ?B ?C}}}, [([0], {{a:A}}), ([1,0], {{b:B}}), ([1,1], {{c:C}})]),
--     --  ({{f:A {a:A} {g:B ?B ?C}}}, [([1,0], {{b:B}}), ([1,1], {{c:C}})]),
--     --  ]
--     TestLabel "Peters Example" $ prune tree1 2 ~?= mtrees1
--     ]

hunit_getMetaLeafCatsList_test =
  let
    -- tree1 in Data.hs
    -- tree2 in Data.hs
    tree3 = TNode "f" (Fun "A" ["A","B"])
      [
        tree1,
        TMeta wildCard
      ]
    tree4 = TNode "f" (Fun "A" ["A","A"])
      [
        tree1,
        tree1
      ]
    tree5 = TNode "f" (Fun "A" ["A","B"])
      [
        TNode "g" (Fun "A" ["A"])
        [
          TNode "g" (Fun "A" ["A"])
          [
            TNode "g" (Fun "A" ["A"])
            [
              tree1
            ]
          ]
        ],
        TMeta "B"
      ]
  in
    TestList [
    TestLabel "Meta" ( getMetaLeafCatsList tree1 ~?= ["A"] ),
    TestLabel "Simple tree without metas" ( getMetaLeafCatsList tree2 ~?= [] ),
    TestLabel "Simple tree 1" ( getMetaLeafCatsList tree3 ~?= ["A",wildCard] ),
    TestLabel "Simple tree 2" ( getMetaLeafCatsList tree4 ~?= ["A","A"] ),
    TestLabel "Tree" ( getMetaLeafCatsList tree5 ~?= ["A","B"] )
    ]

hunit_getMetaPaths_test = 
  let
    -- tree1 in Data.hs
    -- tree2 in Data.hs
    tree3 = TNode "f" (Fun "A" ["A","B"])
      [
        tree1,
        TMeta wildCard
      ]
    tree4 = TNode "f" (Fun "A" ["A","A"])
      [
        tree1,
        tree1
      ]
    tree5 = TNode "f" (Fun "A" ["A","B"])
      [
        TNode "g" (Fun "A" ["A"])
        [
          TNode "g" (Fun "A" ["A"])
          [
            TNode "g" (Fun "A" ["A"])
            [
              TMeta "A"
            ]
          ]
        ],
        TMeta "B"
      ]
  in
    TestList [
    TestLabel "Meta" $ getMetaPaths tree1 ~?= [([],"A")],
    TestLabel "Simple tree without metas" $ getMetaPaths tree2 ~?= [],
    TestLabel "Simple tree" $ getMetaPaths tree3 ~?= [([0],"A"),([1],wildCard)],
    TestLabel "Simple tree" $ getMetaPaths tree4 ~?= [([0],"A"),([1],"A")],
    TestLabel "Tree" $ getMetaPaths tree5 ~?= [([0,0,0,0],"A"),([1],"B")]
    ]

hunit_applyRule_test =
  let
    tree1 = TMeta "A"
    rule1 = Function "f" (Fun "A" ["B","C"])
    tree2 = TNode "f" (Fun "A" ["B","C"]) [TMeta "B",TMeta "C"]
    rule2 = Function "b" (Fun "B" [])
    tree3 = TNode "f" (Fun "A" ["B","C"]) [TNode "b" (Fun "B" []) [],TMeta "C"]
    tree4 = TNode "f" (Fun "A" ["B","C"]) [TMeta "B",TNode "b" (Fun "B" []) []]
    tree5 = TNode "f" (Fun "A" ["B","C"]) [TNode "b" (Fun "B" []) [],TNode "b" (Fun "B" []) []]
  in
    TestList [
    TestLabel "No Pathes given" $ applyRule tree1 rule1 [] ~?= tree1, -- no pathes given, same tree
    TestLabel "Empty Path given, replace whole tree" $ applyRule tree1 rule1 [[]] ~?= tree2,
    TestLabel "Simple application 1" $ applyRule tree2 rule2 [[0]] ~?= tree3,
    TestLabel "Simple application 2" $ applyRule tree2 rule2 [[1]] ~?= tree4,
    TestLabel "Multiple applications" $ applyRule tree2 rule2 [[0],[1]] ~?= tree5,
    TestLabel "Path out of range" $ applyRule tree2 rule2 [[2]] ~?= tree2,
    TestLabel "Path too long" $ applyRule tree2 rule2 [[0,1]] ~?= tree2,
    TestLabel "Ignore superfluous paths" $ applyRule tree2 rule2 [[1],[2],[0,1]] ~?= tree4
             ]
    
hunit_combineToSet_test = 
  let
    tree1 = TMeta "A"
    rule1 = Function "f" (Fun "A" ["B","C"])
    tree2 = TNode "f" (Fun "A" ["B","C"]) [TMeta "B",TMeta "C"] -- read "{f:(B->C->A) {?B} {?C}}" :: TTree
    tree3 = TNode "g" (Fun "A" ["A","B"]) [TMeta "A",TNode "h" (Fun "B" ["B","A"]) [TNode "b" (Fun "B" []) [],TMeta "A"]] -- read "{g:(A->B->A) {?A} {h:(B->A->B) {b:B} {?A}}}" :: TTree
    tree4 = TNode "g" (Fun "A" ["A","B"]) [TNode "f" (Fun "A" ["B","C"]) [TMeta "B",TMeta "C"],TNode "h" (Fun "B" ["B","A"]) [TNode "b" (Fun "B" []) [],TMeta "A"]] -- read "{g:(A->B->A) {f:(B->C->A) {?B} {?C}} {h:(B->A->B) {b:B} {?A}}}" :: TTree
    tree5 = TNode "g" (Fun "A" ["A","B"]) [TMeta "A",TNode "h" (Fun "B" ["B","A"]) [TNode "b" (Fun "B" []) [],TNode "f" (Fun "A" ["B","C"]) [TMeta "B",TMeta "C"]]] -- read "{g:(A->B->A) {?A} {h:(B->A->B) {b:B} {f:(B->C->A) {?B} {?C}}}}" :: TTree
    tree6 = TNode "g" (Fun "A" ["A","B"]) [TNode "f" (Fun "A" ["B","C"]) [TMeta "B",TMeta "C"],TNode "h" (Fun "B" ["B","A"]) [TNode "b" (Fun "B" []) [],TNode "f" (Fun "A" ["B","C"]) [TMeta "B",TMeta "C"]]] -- read "{g:(A->B->A) {f:(B->C->A) {?B} {?C}} {h:(B->A->B) {b:B} {f:(B->C->A) {?B} {?C}}}}" :: TTree
    rule2 = Function "i" (Fun "A" ["A","A"])
    tree7 = TNode "i" (Fun "A" ["A","A"]) [TMeta "A",TMeta "A"] -- read "{i:(A->A->A) {?A} {?A}}" :: TTree
    tree8 = TNode "g" (Fun "A" ["A","B"]) [TNode "i" (Fun "A" ["A","A"]) [TMeta "A",TMeta "A"],TNode "h" (Fun "B" ["B","A"]) [TNode "b" (Fun "B" []) [],TMeta "A"]] -- read "{g:(A -> B -> A) {i:(A -> A -> A) {?A} {?A}} {h:(B -> A -> B) {b:(B)} {?A}}}" :: TTree
    tree9 = TNode "g" (Fun "A" ["A","B"]) [TMeta "A",TNode "h" (Fun "B" ["B","A"]) [TNode "b" (Fun "B" []) [],TNode "i" (Fun "A" ["A","A"]) [TMeta "A",TMeta "A"]]]-- read "{g:(A->B->A) {?A} {h:(B->A->B) {b:B} {i:(A->A->A) {?A} {?A}}}}" :: TTree
    tree10 = TNode "g" (Fun "A" ["A","B"]) [TNode "i" (Fun "A" ["A","A"]) [TMeta "A",TMeta "A"],TNode "h" (Fun "B" ["B","A"]) [TNode "b" (Fun "B" []) [],TNode "i" (Fun "A" ["A","A"]) [TMeta "A",TMeta "A"]]] -- read "{g:(A->B->A) {i:(A->A->A) {?A} {?A}} {h:(B->A->B) {b:B} {i:(A->A->A) {?A} {?A}}}}" :: TTree
  in
    TestList [
    TestLabel "Simple tree, Rule 1, Depth 0, no combination" $ combineToSet tree1 0 rule1 ~?= Set.singleton tree1,
    TestLabel "Simple tree, Rule 1, Depth 1, one combination" $ combineToSet tree1 1 rule1 ~?= fromList [tree2,tree1],
    TestLabel "Simple tree, Rule 1, Depth 2, one combination" $ combineToSet tree1 2 rule1 ~?= fromList [tree2,tree1],
    TestLabel "More complex Rule 1, tree, Depth 0, no combination" $ combineToSet tree3 0 rule1 ~?= Set.singleton tree3,
    TestLabel "More complex Rule 1, tree, Depth 1, no combination" $ combineToSet tree3 1 rule1 ~?= Set.singleton tree3,
    TestLabel "More complex Rule 1, tree, Depth 2, one combination" $ combineToSet tree3 2 rule1 ~?= fromList [tree4,tree3],
    TestLabel "More complex Rule 1, tree, Depth 3, three combination" $ combineToSet tree3 3 rule1 ~?= fromList [tree6,tree5,tree4,tree3],
    TestLabel "More complex Rule 1, tree, Depth 4, three combination" $ combineToSet tree3 4 rule1 ~?= fromList [tree6,tree5,tree4,tree3],
    TestLabel "Simple tree, Rule 2, Depth 0, no combination" $ combineToSet tree1 0 rule2 ~?= Set.singleton tree1,
    TestLabel "Simple tree, Rule 2, Depth 1, one combination" $ combineToSet tree1 1 rule2 ~?= fromList [tree7,tree1],
    TestLabel "Simple tree, Rule 2, Depth 2, one combination" $ combineToSet tree1 2 rule2 ~?= fromList [tree7,tree1],
    TestLabel "More complex Rule 2, tree, Depth 0, no combination" $ combineToSet tree3 0 rule2 ~?= Set.singleton tree3,
    TestLabel "More complex Rule 2, tree, Depth 1, no combination" $ combineToSet tree3 1 rule2 ~?= Set.singleton tree3,
    TestLabel "More complex Rule 2, tree, Depth 2, one combination" $ combineToSet tree3 2 rule2 ~?= fromList [tree8,tree3],
    TestLabel "More complex Rule 2, tree, Depth 3, three combination" $ combineToSet tree3 3 rule2 ~?= fromList [tree10,tree9,tree8,tree3],
    TestLabel "More complex Rule 2, tree, Depth 4, three combination" $ combineToSet tree3 4 rule2 ~?= fromList [tree10,tree9,tree8,tree3]
    ]

hunit_combineToList_test = 
  let
    tree1 = TMeta "A"
    rule1 = Function "f" (Fun "A" ["B","C"])
    tree2 = TNode "f" (Fun "A" ["B","C"]) [TMeta "B",TMeta "C"] -- read "{f:(B->C->A) {?B} {?C}}" :: TTree
    tree3 = TNode "g" (Fun "A" ["A","B"]) [TMeta "A",TNode "h" (Fun "B" ["B","A"]) [TNode "b" (Fun "B" []) [],TMeta "A"]] -- read "{g:(A->B->A) {?A} {h:(B->A->B) {b:B} {?A}}}" :: TTree
    tree4 = TNode "g" (Fun "A" ["A","B"]) [TNode "f" (Fun "A" ["B","C"]) [TMeta "B",TMeta "C"],TNode "h" (Fun "B" ["B","A"]) [TNode "b" (Fun "B" []) [],TMeta "A"]] -- read "{g:(A->B->A) {f:(B->C->A) {?B} {?C}} {h:(B->A->B) {b:B} {?A}}}" :: TTree
    tree5 = TNode "g" (Fun "A" ["A","B"]) [TMeta "A",TNode "h" (Fun "B" ["B","A"]) [TNode "b" (Fun "B" []) [],TNode "f" (Fun "A" ["B","C"]) [TMeta "B",TMeta "C"]]] -- read "{g:(A->B->A) {?A} {h:(B->A->B) {b:B} {f:(B->C->A) {?B} {?C}}}}" :: TTree
    tree6 = TNode "g" (Fun "A" ["A","B"]) [TNode "f" (Fun "A" ["B","C"]) [TMeta "B",TMeta "C"],TNode "h" (Fun "B" ["B","A"]) [TNode "b" (Fun "B" []) [],TNode "f" (Fun "A" ["B","C"]) [TMeta "B",TMeta "C"]]] -- read "{g:(A->B->A) {f:(B->C->A) {?B} {?C}} {h:(B->A->B) {b:B} {f:(B->C->A) {?B} {?C}}}}" :: TTree
    rule2 = Function "i" (Fun "A" ["A","A"])
    tree7 = TNode "i" (Fun "A" ["A","A"]) [TMeta "A",TMeta "A"] -- read "{i:(A->A->A) {?A} {?A}}" :: TTree
    tree8 = TNode "g" (Fun "A" ["A","B"]) [TNode "i" (Fun "A" ["A","A"]) [TMeta "A",TMeta "A"],TNode "h" (Fun "B" ["B","A"]) [TNode "b" (Fun "B" []) [],TMeta "A"]] -- read "{g:(A -> B -> A) {i:(A -> A -> A) {?A} {?A}} {h:(B -> A -> B) {b:(B)} {?A}}}" :: TTree
    tree9 = TNode "g" (Fun "A" ["A","B"]) [TMeta "A",TNode "h" (Fun "B" ["B","A"]) [TNode "b" (Fun "B" []) [],TNode "i" (Fun "A" ["A","A"]) [TMeta "A",TMeta "A"]]]-- read "{g:(A->B->A) {?A} {h:(B->A->B) {b:B} {i:(A->A->A) {?A} {?A}}}}" :: TTree
    tree10 = TNode "g" (Fun "A" ["A","B"]) [TNode "i" (Fun "A" ["A","A"]) [TMeta "A",TMeta "A"],TNode "h" (Fun "B" ["B","A"]) [TNode "b" (Fun "B" []) [],TNode "i" (Fun "A" ["A","A"]) [TMeta "A",TMeta "A"]]] -- read "{g:(A->B->A) {i:(A->A->A) {?A} {?A}} {h:(B->A->B) {b:B} {i:(A->A->A) {?A} {?A}}}}" :: TTree
  in
    TestList [
    TestLabel "Simple tree, Rule 1, Depth 0, no combination" $ combineToList tree1 0 rule1 ~?= [tree1],
    TestLabel "Simple tree, Rule 1, Depth 1, one combination" $ combineToList tree1 1 rule1 ~?= [tree1,tree2],
    TestLabel "Simple tree, Rule 1, Depth 2, one combination" $ combineToList tree1 2 rule1 ~?= [tree1,tree2],
    TestLabel "More complex Rule 1, tree, Depth 0, no combination" $ combineToList tree3 0 rule1 ~?= [tree3],
    TestLabel "More complex Rule 1, tree, Depth 1, no combination" $ combineToList tree3 1 rule1 ~?= [tree3],
    TestLabel "More complex Rule 1, tree, Depth 2, one combination" $ combineToList tree3 2 rule1 ~?= [tree3,tree4],
    TestLabel "More complex Rule 1, tree, Depth 3, three combination" $ combineToList tree3 3 rule1 ~?= [tree3,tree5,tree4,tree6],
    TestLabel "More complex Rule 1, tree, Depth 4, three combination" $ combineToList tree3 4 rule1 ~?= [tree3,tree5,tree4,tree6],
    TestLabel "Simple tree, Rule 2, Depth 0, no combination" $ combineToList tree1 0 rule2 ~?= [tree1],
    TestLabel "Simple tree, Rule 2, Depth 1, one combination" $ combineToList tree1 1 rule2 ~?= [tree1,tree7],
    TestLabel "Simple tree, Rule 2, Depth 2, one combination" $ combineToList tree1 2 rule2 ~?= [tree1,tree7],
    TestLabel "More complex Rule 2, tree, Depth 0, no combination" $ combineToList tree3 0 rule2 ~?= [tree3],
    TestLabel "More complex Rule 2, tree, Depth 1, no combination" $ combineToList tree3 1 rule2 ~?= [tree3],
    TestLabel "More complex Rule 2, tree, Depth 2, one combination" $ combineToList tree3 2 rule2 ~?= [tree3,tree8],
    TestLabel "More complex Rule 2, tree, Depth 3, three combination" $ (sort $ combineToList tree3 3 rule2) ~?= sort [tree10,tree9,tree8,tree3],
    TestLabel "More complex Rule 2, tree, Depth 4, three combination" $ (sort $ combineToList tree3 4 rule2) ~?= sort [tree10,tree9,tree8,tree3]
    ]    

hunit_extendTree_test = 
  let
    grammar1 = emptyGrammar
    grammar2 = Grammar "A" [] [] emptyPGF
    tree1 = TMeta "A"
    grammar3 = Grammar "A"
      [
        Function "f" (Fun "A" ["A"])
      ]
      []
      emptyPGF
    tree2 = TNode "f" (Fun "A" ["A"]) [TMeta "A"]
    grammar4 = Grammar "A"
      [
        Function "f" (Fun "A" ["A"]),
        Function "g" (Fun "A" ["A","A"]),
        Function "h" (Fun "A" ["B","C"]),
        Function "i" (Fun "A" ["B"]),
        Function "k" (Fun "B" ["A"])
      ]
      []
      emptyPGF
    tree3 = TNode "g" (Fun "A" ["A","A"]) [TMeta "A",TMeta "A"]
    tree4 = TNode "h" (Fun "A" ["B","C"]) [TMeta "B",TMeta "C"]
    tree5 = TNode "i" (Fun "A" ["B"]) [TMeta "B"]
    tree6 = TNode "i" (Fun "A" ["B"]) [TNode "k" (Fun "B" ["A"]) [TMeta "A"]]
    tree7 = TNode "i" (Fun "A" ["A","A"]) [TMeta "A",TNode "f" (Fun "A" ["A"]) [TMeta "A"]]
    tree8 = TNode "i" (Fun "A" ["A","A"]) [TNode "f" (Fun "A" ["A"]) [TMeta "A"],TNode "f" (Fun "A" ["A"]) [TMeta "A"]]
    tree9 = TNode "i" (Fun "A" ["A","A"]) [TMeta "A",TNode "f" (Fun "A" ["A"]) [TNode "f" (Fun "A" ["A"]) [TMeta "A"]]]
    tree10 = TNode "i" (Fun "A" ["A","A"]) [TNode "f" (Fun "A" ["A"]) [TMeta "A"],TNode "f" (Fun "A" ["A"]) [TNode "f" (Fun "A" ["A"]) [TMeta "A"]]] -- MetaTTree (read "{i:(A->A->A) {f:(A->A) {?A}} {f:(A->A) {f:(A->A) {?A}}}}" :: TTree)
  in
    TestList [
    TestLabel "Empty grammar depth 0" ( extendTree grammar1 tree1 0 ~?= empty ),
    TestLabel "Empty grammar depth 1" ( extendTree grammar1 tree1 1 ~?= empty  ),
    TestLabel "Grammar without rules depth 0" ( extendTree grammar2 tree1 0 ~?= empty ),
    TestLabel "Grammar without rules depth 1" ( extendTree grammar2 tree1 0 ~?= empty ),
    TestLabel "Simple Grammar 3 tree 1 depth 0" ( extendTree grammar3 tree1 0 ~?= singleton tree1 ),
    TestLabel "Simple Grammar 3 tree 1 depth 1" ( extendTree grammar3 tree1 1 ~?= fromList [tree1,tree2] ),
    TestLabel "Simple Grammar 3 tree 1 depth 2" ( extendTree grammar3 tree1 2 ~?= fromList [tree1,tree2] ),
    TestLabel "Simple Grammar 3 tree 1 depth 3" ( extendTree grammar3 tree1 3 ~?= fromList [tree1,tree2] ),
    TestLabel "Simple Grammar 4 tree 1 depth 0" ( extendTree grammar4 tree1 0 ~?= singleton tree1 ),
    TestLabel "Simple Grammar 4 tree 1 depth 1" ( extendTree grammar4 tree1 1 ~?= fromList [tree1,tree2,tree3,tree4,tree5] ),
    TestLabel "Simple Grammar 4 tree 1 depth 2" ( extendTree grammar4 tree1 2 ~?= fromList [tree1,tree2,tree3,tree4,tree5] ),
    TestLabel "Simple Grammar 4 tree 1 depth 3" ( extendTree grammar4 tree1 3 ~?= fromList [tree1,tree2,tree3,tree4,tree5] ),
    TestLabel "Simple Grammar 3 tree 7 depth 0" ( extendTree grammar3 tree7 0 ~?= singleton tree7 ),
    TestLabel "Simple Grammar 3 tree 7 depth 1" ( extendTree grammar3 tree7 1 ~?= singleton tree7 ),
    TestLabel "Simple Grammar 3 tree 7 depth 2" ( extendTree grammar3 tree7 2 ~?= fromList [tree7,tree8] ),
    TestLabel "Simple Grammar 3 tree 7 depth 3" ( extendTree grammar3 tree7 3 ~?= fromList [tree7,tree8,tree9,tree10] ),
    TestLabel "Simple Grammar 3 tree 7 depth 4" ( extendTree grammar3 tree7 4 ~?= fromList [tree7,tree8,tree9,tree10] )
    ]

-- To be fixed
-- hunit_generate_test = 
--   let
--     grammar =
--       Grammar
--       "A"
--       [
--         Function "f" (Fun "A" ["A", "B"]),
--         Function "g" (Fun ("B") ["B", "C"])
--       ]
--       [
--         Function "a" (Fun "A" []),
--         Function "b" (Fun ("B") []),
--         Function "c" (Fun ("C") [])
--       ]
--       emptyPGF
--     result = fromList
--       [
--         MetaTTree (read "{?A}") $ fromList [([], read "{?A}")],
--         MetaTTree (read "{a:A}") empty,
--         MetaTTree (read "{f:A {?A} {?B}}") $ fromList [([0], read "{?A}"), ([1], read "{?B}")],
--         MetaTTree (read "{f:A {a:A} {?B}}") $ fromList [([1], read "{?B}")],
--         MetaTTree (read "{f:A {f:A {?A} {?B}} {?B}}") $ fromList [([0,0], read "{?A}"), ([0,1], read "{?B}"), ([1], read "{?B}")],
--         MetaTTree (read "{f:A {?A} {b:B}") $ fromList [([0], read "{?A}")],
--         MetaTTree (read "{f:A {?A} {g:B {?B} {?C}}}") $ fromList [([0], read "{?A}"),([1,0], read "{?B}"),([1,1], read "{?C}")],
--         MetaTTree (read "{f:A {a:A} {b:B}}") empty,
--         MetaTTree (read "{f:A {a:A} {g:B {?B} {?C}}}") $ fromList [([1,0], read "{?B}"),([1,1], read "{?C}")],
--         MetaTTree (read "{f:A {f:A {?A} {?B}} {b:B}}") $ fromList [([0,0], read "{?A}"), ([0,1], read "{?B}")],
--         MetaTTree (read "{f:A {f:A {?A} {?B}} {g:B {?B} {?C}}}") $ fromList [([0,0], read "{?A}"), ([0,1], read "{?B}"),([1,0], read "{?B}"), ([1,1], read "{?C}")]
--       ]:: Set MetaTTree
--   in
--   TestList [
--     TestLabel "Peters example" $ Muste.Tree.Internal.generate grammar (startcat grammar) 2 ~?= result
--            ]
  

hunit_computeCosts_test = 
  let
    tree1 = TMeta "A" -- read "{?A}" :: TTree
    tree2 = TMeta "B" -- read "{?B}" :: TTree
    tree3 = TNode "f" (Fun "A" ["A"]) [TMeta "A"] -- read "{f:(A->A) {?A}}" :: TTree
    tree4 = TNode "f" (Fun "A" ["A"]) [TNode "a" (Fun "A" []) []] -- read "{f:(A->A) {a:A}}" :: TTree
  in
    TestList [
    TestLabel "Meta and no deleted trees 1" $ computeCosts tree1 tree1 [] ~?= 0,
    TestLabel "Meta and no deleted trees 2" $ computeCosts tree1 tree2 [] ~?= 0,
    TestLabel "Meta and no deleted trees 3" $ computeCosts tree2 tree1 [] ~?= 0,
    TestLabel "Meta and deleted Meta" $ computeCosts tree1 tree1 [tree1] ~?= 0,
    TestLabel "Combination of Trees with total cost 1 1" $ computeCosts tree3 tree1 [tree1] ~?= 1,
    TestLabel "Combination of Trees with total cost 1 2" $ computeCosts tree1 tree3 [tree1] ~?= 1,
    TestLabel "Combination of Trees with total cost 1 3" $ computeCosts tree1 tree1 [tree3] ~?= 1,
    TestLabel "Combination of Trees with total cost 2" $ computeCosts tree1 tree1 [tree4] ~?= 2,
    TestLabel "Combination of Trees with total cost 3 1" $ computeCosts tree4 tree3 [tree1] ~?= 3,
    TestLabel "Combination of Trees with total cost 3 2" $ computeCosts tree4 tree1 [tree3] ~?= 3,
    TestLabel "Combination of Trees with total cost 3 3" $ computeCosts tree3 tree4 [tree1] ~?= 3,
    TestLabel "Combination of Trees with total cost 3 4" $ computeCosts tree3 tree1 [tree4] ~?= 3,
    TestLabel "Combination of Trees with total cost 3 5" $ computeCosts tree1 tree4 [tree3] ~?= 3,
    TestLabel "Combination of Trees with total cost 3 6" $ computeCosts tree1 tree3 [tree4] ~?= 3
    ]

hunit_combineTrees_test =
  TestList [
  -- TestLabel "Incompatible Metas 1" ( combineTrees (read "{?A}") [read "{?B}"] ~?= [read "{?A}"] ),
    TestLabel "Incompatible Metas 1" ( combineTrees (TMeta "A") [TMeta "B"] ~?= [TMeta "A"] ),
--    TestLabel "Incompatible Metas 2" ( combineTrees (read "{?B}") [read "{?A}"] ~?= [read "{?B}"] ),
    TestLabel "Incompatible Metas 2" ( combineTrees (TMeta "B") [TMeta "A"] ~?= [TMeta "B"] ),
--    TestLabel "Incompatible Trees" ( combineTrees (read "{f:(A->A) {?A}}") [read "{b:B}"] ~?= [read "{f:(A->A) {?A}}"] ),
    TestLabel "Incompatible Trees" ( combineTrees (TNode "f" (Fun "A" ["A"]) [TMeta "A"]) [TNode "b" (Fun "B" []) []] ~?= [TNode "f" (Fun "A" ["A"]) [TMeta "A"]] ),
--    TestLabel "Complete Tree" ( combineTrees (read "{f:(A->A) {a:A}}") [read "{a:A}"] ~?= [read "{f:(A->A) {a:A}}"] ),
    TestLabel "Complete Tree" ( combineTrees (TNode "f" (Fun "A" ["A"]) [TNode "a" (Fun "A" []) []]) [TNode "a" (Fun "A" []) []] ~?= [TNode "f" (Fun "A" ["A"]) [TNode "a" (Fun "A" []) []]] ),
--    TestLabel "Compatible Trees 1" ( combineTrees (read "{?A}") [read "{a:A}"] ~?= [read "{a:A}"] ),
    TestLabel "Compatible Trees 1" ( combineTrees (TMeta "A") [TNode "a" (Fun "A" []) []] ~?= [TNode "a" (Fun "A" []) []] ),
--    TestLabel "Compatible Trees 2" ( combineTrees (read "{f:(A->A) {?A}}") [read "{a:A}"] ~?= [read "{f:(A->A) {a:A}}"] ),
    TestLabel "Compatible Trees 2" ( combineTrees (TNode "f" (Fun "A" ["A"]) [TMeta "A"]) [TNode "a" (Fun "A" []) []] ~?= [TNode "f" (Fun "A" ["A"]) [TNode "a" (Fun "A" []) []]])
    -- To be fixed
    -- TestLabel "Multiple Compatible Trees 1" ( combineTrees (read "{f:(A->A) {?A}}") [read "{?A}",read "{f:(A->A) {?A}}"] ~?= [read "{f:(A->A) {?A}}",read "{f:(A->A) {f:(A->A) {?A}}}"] ),
    -- -- TestLabel "Multiple Compatible Trees 2" ( combineTrees (read "{f:(A->A) {?A}}") [read "{f:(A->A) {?A}}",read "{f:(A->A) {a:A}}"] ~?= [read "{f:(A->A) {f:(A->A) {?A}}}",read "{f:(A->A) {f:(A->A) {a:A}}}"] ),
    -- TestLabel "Multiple Compatible Trees 2" ( combineTrees (TNode "f" (Fun "A" ["A"]) [TNode "a" (Fun "A" []) []]) [read "{f:(A->A) {?A}}",read "{f:(A->A) {a:A}}"] ~?= [read "{f:(A->A) {f:(A->A) {?A}}}",read "{f:(A->A) {f:(A->A) {a:A}}}"] ),
    -- TestLabel "Compatible Trees 3" ( combineTrees (read "{f:(A->B->A) {?A} {?B}}") [read "{a:A}"] ~?= [read "{f:(A->B->A) {a:A} {?B}}"] ),
    -- TestLabel "Compatible Trees 4" ( combineTrees (read "{f:(A->B->A) {?A} {?B}}") [read "{a:A}",read "{b:B}"] ~?= [read "{f:(A->B->A) {a:A} {b:B}}"] ), 
    -- TestLabel "Multiple Compatible Trees 1" ( combineTrees (read "{f:(A->A->A) {?A} {?A}}") [read "{a:A}"] ~?= [read "{f:(A->A->A) {a:A} {?A}}",read "{f:(A->A->A) {?A} {a:A}}"] ),
    -- TestLabel "Multiple Compatible Trees 2" ( combineTrees (read "{f:(A->B->A) {?A} {?B}}") [read "{a:A}",read "{b:B}",read "{b2:B}"] ~?= [read "{f:(A->B->A) {a:A} {b:B}}",read "{f:(A->B->A) {a:A} {b2:B}}"] )
    ]

-- To be removed
-- hunit_match_test = 
--   let
--     tree11 = (MetaTTree (read "{f:(A -> B -> A) {?A} {?B}}") $ fromList [([0], read "{a:A}"), ([1], read "{g:(B -> C -> B) {b:B} {c:C}}")])
--     tree12 = (MetaTTree (read "{f:(A -> B -> A) {f:(A -> B -> A) {?A} {?B}} {b:B}}") $ fromList [([0,0], read "{?A}"), ([0,1], read "{?B}")])
--     result1 = (1+3, read "{f:(A -> B -> A) {f:(A -> B -> A) {a:A} {g:(B -> C -> B) {b:B} {c:C}}} {b:B}}") :: (Cost,TTree)
--     tree21 = (MetaTTree (read "{f:A {?A} {?B}}") $ fromList [([0], read "{a:A}"), ([1], read "{g:B {b:B} {c:C}}")])
--     tree22 = (MetaTTree (read "{f:A {?A} {b:B}}") $ fromList [([0], read "{?A}")])
--     result2 = (1+2+3, read "{f:A {a:A} {b:B}}") :: (Cost,TTree)
--   in
--     TestList [
--     TestLabel "Peters example 1" ( head ( match tree11 tree12 ) ~?= result1 ),
--     TestLabel "Peters example 2" ( head ( match tree21 tree22 ) ~?= result2 )
--     ]
  
show_tests =
  TestList [
  TestLabel "Show TTree show" hunit_Show_TTree_show_test
--  TestLabel "Show MetaTTree show" hunit_Show_MetaTTree_show_test
  ]

-- read_tests =
--   TestList [
--   hunit_Read_TTree_readsPrec_test
--   ]

treec_tests =
  TestList [
  TestLabel "TreeC GFAbsTree showTree" hunit_TreeC_GFAbsTree_showTree_test,
  TestLabel "TreeC GFAbsTree selectNode" hunit_TreeC_GFAbsTree_selectNode_test,
  TestLabel "TreeC GFAbsTree selectBranch" hunit_TreeC_GFAbsTree_selectBranch_test,
  TestLabel "TreeC TTree showTree" hunit_TreeC_TTree_showTree_test,
  TestLabel "TreeC TTree selectNode" hunit_TreeC_TTree_selectNode_test,
  TestLabel "TreeC TTree selectBranch" hunit_TreeC_TTree_selectBranch_test
  ]
  
tree_function_tests =
  TestList [
--  TestLabel "consumeChar" hunit_consumeChar_test,
--  TestLabel "readFunType" hunit_readFunType_test,
  TestLabel "getChildCats" hunit_getChildCats_test,
  TestLabel "checkType" hunit_checkType_test,
  TestLabel "fixTypes" hunit_fixTypes_test,
--  TestLabel "readTree" hunit_readTree_test,
--  TestLabel "readTree" hunit_readTrees_test,
  TestLabel "isMeta" hunit_isMeta_test,
  TestLabel "getTreeCat" hunit_getTreeCat_test,
  TestLabel "gfAbsTreeToTTreeWithPGF" hunit_gfAbsTreeToTTreeWithPGF_test,
  TestLabel "gfAbsTreeToTTreeWithGrammar" hunit_gfAbsTreeToTTreeWithGrammar_test,
  TestLabel "ttreeTogfAbsTree" hunit_ttreeToGFAbsTree_test,
  TestLabel "ttreeToLTree" hunit_ttreeToLTree_test,
  TestLabel "showBracket" hunit_showBracket_test,
  TestLabel "getPath" hunit_getPath_test,
  TestLabel "maxDepth" hunit_maxDepth_test,
  TestLabel "countNodes" hunit_countNodes_test,
--  TestLabel "makeMeta" hunit_makeMeta_test,
  TestLabel "replaceBranch" hunit_replaceBranch_test,
  TestLabel "replaceNode" hunit_replaceNode_test,
  TestLabel "getMetaLeafCatsSet" hunit_getMetaLeafCatsSet_test,
  TestLabel "getMetaLeafCatsSet"  hunit_getMetaLeafCatsList_test,
--  TestLabel "replaceNodeByMeta" hunit_replaceNodeByMeta_test,
  TestLabel "maxPath" hunit_maxPath_test,
  TestLabel "findPaths" hunit_findPaths_test,
  TestLabel "findLeafPaths" hunit_findLeafPaths_test,
--  TestLabel "prune" hunit_prune_test,
  TestLabel "getMetaPaths" hunit_getMetaPaths_test,
  TestLabel "applyRule" hunit_applyRule_test,
  TestLabel "combineToSet" hunit_combineToSet_test,
  TestLabel "combineToList" hunit_combineToList_test,
  TestLabel "extendTree" hunit_extendTree_test,
--  TestLabel "generate" hunit_generate_test,
  TestLabel "computeCosts" hunit_computeCosts_test,
  TestLabel "combineTrees" hunit_combineTrees_test
--  TestLabel "match" hunit_match_test
  ]

list_function_tests =
  TestList [
  TestLabel "ListReplace" hunit_listReplace_test,
  TestLabel "powerList" hunit_powerList_test
  ]
  
hunit_tests = TestList [
  treec_tests,
  show_tests,
--   read_tests,
  tree_function_tests,
  list_function_tests
  ]

-- | Finds paths for all meta nodes
prop_metaPathsForAllMetaCats :: TTree -> Bool
prop_metaPathsForAllMetaCats tree =
  getMetaLeafCatsSet tree == fromList (map snd (getMetaPaths tree))

-- | Meta paths not empty when tree has meta nodes
prop_metasHaveMetaPaths :: TTree -> Property
prop_metasHaveMetaPaths tree = hasMetas tree ==> not $ null $ getMetaPaths tree


-- Conversion between GFAbsTrees and TTrees
quickcheck_tests :: [(TestName,Property)]
quickcheck_tests = [
  ("Meta paths 1",property prop_metaPathsForAllMetaCats)
--  ("Meta paths 2",property prop_metasHaveMetaPaths)  -- Fails because there are no metas
  ]

