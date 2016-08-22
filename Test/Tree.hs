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
    TestLabel "Existing Path 1" $ selectNode tree [0,0,0] ~?= Just (EFun (mkCId "1")),
    TestLabel "Existing Path 2" $ selectNode tree [0,0,1,0] ~?= Just (EFun (mkCId "2")),
    TestLabel "Path too deep" $ selectNode tree [0,0,0,0] ~?= Nothing,
    TestLabel "Branch out of range" $ selectNode tree [0,2] ~?= Nothing, 
    TestLabel "Negative Branch" $ selectNode tree [-1] ~?= Nothing
    ]

hunit_TreeC_GFAbsTree_selectBranch_test =
  let
    tree = (EApp (EFun (mkCId "1")) (EFun (mkCId "2")))
  in
    TestList [
    TestLabel "Existing Branch 1" $ selectBranch tree 0 ~?= Just (EFun (mkCId "1")),
    TestLabel "Existing Branch 2" $ selectBranch tree 1 ~?= Just (EFun (mkCId "2")),
    TestLabel "Negative Branch" $ selectBranch tree (-1) ~?= Nothing,
    TestLabel "Branch out of range" $ selectBranch tree 2 ~?= Nothing
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
    TestLabel "Meta tree" $ showTree tree1 ~?= "{?A}",
    TestLabel "Simple tree with metas" $ showTree tree2 ~?= "{f:(A -> B -> A) {?A} {?B}}",
    TestLabel "Simple tree" $ showTree tree3 ~?= "{f:(A -> B -> A) {a:(A)} {b:(B)}}"
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
    TestLabel "Existing Path" $ selectNode tree [1,0] ~?= Just ( TNode (mkCId "b") (Fun (mkCId "B") []) [] ),
    TestLabel "Path too deep" $ selectNode tree [1,1,1] ~?= Nothing,
    TestLabel "Branch out of range" $ selectNode tree [0,2] ~?= Nothing, 
    TestLabel "Negative Branch" $ selectNode tree [-1] ~?= Nothing
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
    TestLabel "Existing Branch 1" $ selectBranch tree 0 ~?= Just (TNode (mkCId "a") (Fun (mkCId "A") []) []),
    TestLabel "Existing Branch 2" $ selectBranch tree 1 ~?= Just (TNode (mkCId "b") (Fun (mkCId "B") []) []),
    TestLabel "Existing Branch 2" $ selectBranch tree 2 ~?= Just (TNode (mkCId "c") (Fun (mkCId "C") []) []) ,
    TestLabel "Negative Branch" $ selectBranch tree (-1) ~?= Nothing,
    TestLabel "Branch out of range" $ selectBranch tree 3 ~?= Nothing 
    ]

hunit_Show_TTree_show_test =
  let
    tree1 = TMeta (mkCId "A")
    str1 = "{?A}"
    tree2 = TMeta wildCId
    str2 = "{?_}"
    tree3 = TNode (mkCId "a") NoType []
    str3 = "{a:()}"
    tree4 = TNode (mkCId "a") (Fun (mkCId "A") []) []
    str4 = "{a:(A)}"
    tree5 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TMeta (mkCId "A")),(TMeta (mkCId "B"))]
    str5 = "{f:(A -> B -> A) {?A} {?B}}"
    tree6 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TNode (mkCId "a") (Fun (mkCId "A") []) []),(TNode (mkCId "b") (Fun (mkCId "B") []) [])]
    str6 = "{f:(A -> B -> A) {a:(A)} {b:(B)}}"
    tree7 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "B")]) [(TNode (mkCId "g") (Fun (mkCId "B") [(mkCId "A")]) [(TNode (mkCId "a") (Fun (mkCId "A") []) [])])]
    str7 = "{f:(B -> A) {g:(A -> B) {a:(A)}}}"
  in
    TestList [
    TestLabel "Simple Meta" $ show tree1 ~?= str1,
    TestLabel "Wildcard Meta" $ show tree2 ~?= str2,
    TestLabel "Simple tree without type" $ show tree3 ~?= str3,
    TestLabel "Simple tree" $ show tree4 ~?= str4,
    TestLabel "More complex tree with metas" $ show tree5 ~?= str5,
    TestLabel "More complex tree" $ show tree6 ~?= str6 ,
    TestLabel "Deep Tree" $ show tree7 ~?= str7
    ]

hunit_Show_MetaTTree_show_test =
  let
    tree1 = MetaTTree (TMeta (mkCId "A")) (fromList [([0],TNode (mkCId "a") (Fun (mkCId "A") []) [])])
    str1 = "({?A}, [([0],{a:(A)})])"
    tree2 = MetaTTree (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TMeta (mkCId "A")),(TMeta (mkCId "B"))])
      (fromList [
          ([0],TNode (mkCId "a") (Fun (mkCId "A") []) []),
          ([1],TNode (mkCId "b") (Fun (mkCId "B") []) [])
          ])
    str2 = "({f:(A -> B -> A) {?A} {?B}}, [([0],{a:(A)}) ([1],{b:(B)})])"
    tree3 = MetaTTree (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "B")]) [(TNode (mkCId "g") (Fun (mkCId "B") [(mkCId "A")]) [(TMeta(mkCId "A"))])])
      (fromList [([0,0,0],(TNode (mkCId "a") (Fun (mkCId "A") []) []))])
    str3 = "({f:(B -> A) {g:(A -> B) {?A}}}, [([0,0,0],{a:(A)})])"
  in
    TestList [
    TestLabel "Simple tree with one pruned branch" $ show tree1 ~?= str1,
    TestLabel "Simple tree with two pruned branches" $ show tree2 ~?= str2,
    TestLabel "Deep tree" $ show tree3 ~?= str3
    ]
  
hunit_consumeChar_test =
  let
    empty = ""
    match = " 12345"
    matched = "12345"
    nonmatch = "_12345"
  in
    TestList [
    TestLabel "Empty String" $ consumeChar ' ' empty ~?= empty,
    TestLabel "Matching String" $ consumeChar ' ' match ~?= matched,
    TestLabel "Non-Matching String" $ consumeChar ' ' nonmatch ~?= nonmatch
    ]

hunit_readFunType_test =
  let
    str1 = "A"
    str2 = "(A)"
    type1 = (Fun (mkCId "A") [])
    str3 = "A->B"
    str4 = "A -> B"
    str5 = "(A->B)"
    str6 = "(A -> B)"
    str7 = "( A -> B )"
    type2 = (Fun (mkCId "B") [(mkCId "A")])
    str8 = ""
    str9 = "_"
    str10 = "###"
    str11 = "->"
    str12 = "-> A"
    str13 = "A ->"
  in
    TestList [
    TestLabel "Simple Type 1" $ ( readFunType str1 ~?= Just (type1, "") ),
    TestLabel "Simple Type 2" $ ( readFunType str2 ~?= Just (type1, "") ),
    TestLabel "Simple Type with rest 1" $ ( readFunType ( str2 ++ "###" ) ~?= Just (type1, "###") ),
    TestLabel "Simple Type with rest 2" $ ( readFunType ( str2 ++ "   ###" ) ~?= Just (type1, "   ###") ),
    TestLabel "Function Type 1" $ ( readFunType str3 ~?= Just (type2, "") ),
    TestLabel "Function Type 2" $ ( readFunType str4 ~?= Just (type2, "") ),
    TestLabel "Function Type 3" $ ( readFunType str5 ~?= Just (type2, "") ),
    TestLabel "Function Type 4" $ ( readFunType str6 ~?= Just (type2, "") ),
    TestLabel "Function Type 5" $ ( readFunType str7 ~?= Just (type2, "") ),
    TestLabel "Function Type with rest 1" $ ( readFunType ( str6 ++ "###" ) ~?= Just (type2, "###") ),
    TestLabel "Function Type with rest 2" $ ( readFunType ( str6 ++ "   ###" ) ~?= Just (type2, "   ###") ),
    TestLabel "Empty String" $ ( readFunType ( str8 ) ~?= Nothing ),
    TestLabel "Wildcard" $ ( readFunType ( str9 ) ~?= Nothing ),
    TestLabel "Three Hashes" $ ( readFunType ( str10 ) ~?= Nothing ),
    TestLabel "Arrow" $ ( readFunType ( str11 ) ~?= Nothing ),
    TestLabel "Arrow A" $ ( readFunType ( str12 ) ~?= Just (type1, "") ),
    TestLabel "A Arrow" $ ( readFunType ( str13 ) ~?= Just (type1, "") )
    ]

hunit_getChildCats_test =
  let
    tree1 = TMeta (mkCId "A")
    tree2 = TNode (mkCId "a") (Fun (mkCId "A") []) []
    tree3 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TMeta (mkCId "A")),(TMeta (mkCId "B"))]
    tree4 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TNode (mkCId "a") (Fun (mkCId "A") []) []) ,(TNode (mkCId "b") (Fun (mkCId "B") []) [])]
  in
    TestList [
    TestLabel "Meta node" $ getChildCats tree1 ~?= [],
    TestLabel "Simple tree without subtrees" $ getChildCats tree2 ~?= [],
    TestLabel "Simple tree with meta nodes" $ getChildCats tree3 ~?= [(mkCId "A"),(mkCId "B")],
    TestLabel "Simple tree with nodes" $ getChildCats tree4 ~?= [(mkCId "A"),(mkCId "B")]
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
    TestLabel "Meta node" $ checkType tree1 ~?= True,
    TestLabel "Simple tree without subtrees" $ checkType tree2 ~?= True,
    TestLabel "Simple tree with meta nodes" $ checkType tree3 ~?= True,
    TestLabel "Simple tree with nodes" $ checkType tree4 ~?= True,
    TestLabel "Simple tree with meta nodes" $ checkType tree5 ~?= False,
    TestLabel "Simple tree with nodes" $ checkType tree6 ~?= False,
    TestLabel "Deep tree with nodes" $ checkType tree7 ~?= False
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
    TestLabel "Fixable tree" $ fixTypes tree1 ~?= tree2,
    TestLabel "Already fixed tree" $ fixTypes tree2 ~?= tree2,
    TestLabel "Deep tree" $ fixTypes tree3 ~?= tree4,
    TestCase $ assertBool "Already fixed tree with type errors" $ fixTypes tree5 /= tree2 && fixTypes tree5 == tree5
    ]
    
hunit_readTree_test =
  let
    str1 = ""
    str2 = "{}"
    str3 = "_"
    str4 = "?"
    str5 = "###"
    str6 = "{a:A}"
    tree1 = (TNode (mkCId "a") (Fun (mkCId "A") []) [])
    str7 = "{a:A"
    str8 = "a:A}"
    str9 = "a:A"
    str10 = "{f:(A -> B -> A) {a:A} {b:B}}"
    tree2 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
      [
        (TNode (mkCId "a") (Fun (mkCId "A") []) []),
        (TNode (mkCId "b") (Fun (mkCId "B") []) [])
      ]
    str11 = "{f:(A -> A) {f:(A -> A) {f:(A -> A) {f:(A -> A) {a:A}}}}}"
    tree3 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A")])
      [
        TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A")])
        [
          TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A")])
          [
            TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A")])
            [
              TNode (mkCId "a") (Fun (mkCId "A") []) []
            ]
          ]
        ]
      ]
    str12 = "?A"
    str13 = "{?A}"
    tree4 = TMeta (mkCId "A")
    str14 = "{f:(A -> B -> A) {?A} {?B}}"
    tree5 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
      [
        (TMeta (mkCId "A")),
        (TMeta (mkCId "B"))
      ]
  in
    TestList [
    TestLabel "Empty String" $ readTree str1 ~?= Nothing,
    TestLabel "Curly Brackets" $ readTree str2 ~?= Nothing,
    TestLabel "Wildcard" $ readTree str3 ~?= Nothing,
    TestLabel "Questionmark" $ readTree str4 ~?= Nothing,
    TestLabel "Three Hashes" $ readTree str5 ~?= Nothing,
    TestLabel "Simple Tree" $ readTree str6 ~?= Just (tree1,""),
    TestLabel "Partial Simple Tree 1" $ readTree str7 ~?= Just (tree1,""),
    TestLabel "Partial Simple Tree 2" $ readTree str8 ~?= Just (tree1,""),
    TestLabel "Partial Simple Tree 3" $ readTree str9 ~?= Just (tree1,""),
    TestLabel "Slightly more complex Tree" $ readTree str10 ~?= Just (tree2,""),
    TestLabel "Slightly more complex Tree" $ readTree str11 ~?= Just (tree3,""),
    TestLabel "Simple Meta Tree 1" $ readTree str12 ~?= Just (tree4,""),
    TestLabel "Simple Meta Tree 2" $ readTree str13 ~?= Just (tree4,""),
    TestLabel "More complex Meta Tree" $ readTree str14 ~?= Just (tree5,""),
    TestLabel "Simple Tree with rest" $ readTree (str7 ++ "###") ~?= Just (tree1,"###"),
    TestLabel "Simple Tree with rest" $ readTree (str7 ++ "   ###") ~?= Just (tree1,"###") -- Slightly unexpected
    ]

hunit_readTrees_test =
  let
    str1 = ""
    str2 = "{} {}"
    str3 = "{a:A} {b:B}"
    trees1 = [(TNode (mkCId "a") (Fun (mkCId "A") []) []),(TNode (mkCId "b") (Fun (mkCId "B") []) [])]
    str4 = "{f:(A -> B -> A) {a:A} {b:B}} {g:(B -> C -> B) {b:B} {c:C}}"
    trees2 =
      [
        (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
         [
           (TNode (mkCId "a") (Fun (mkCId "A") []) []),
           (TNode (mkCId "b") (Fun (mkCId "B") []) [])
         ]
        ),
        (TNode (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")])
         [
           (TNode (mkCId "b") (Fun (mkCId "B") []) []),
           (TNode (mkCId "c") (Fun (mkCId "C") []) [])
         ]
        )
      ]
    str5 = "{a:A} {?B}"
    trees3 =
      [
        TNode (mkCId "a") (Fun (mkCId "A") []) [],
        TMeta (mkCId "B")
      ]
    str6 = "{?A} {b:B}"
    trees4 =
        [
        TMeta (mkCId "A"),
        TNode (mkCId "b") (Fun (mkCId "B") []) []
      ]
  in
    TestList [
    TestLabel "Empty String" $ readTrees str1 ~?= ([],""),
    TestLabel "Curly Brackets" $ readTrees str2 ~?= ([],"{} {}"),
    TestLabel "Simple Trees" $ readTrees str3 ~?= (trees1,""),
    TestLabel "Slightly more complex Trees" $ readTrees str4 ~?= (trees2,""),
    TestLabel "Some Metas 1" $ readTrees str5 ~?= (trees3,""),
    TestLabel "Some Metas 2" $ readTrees str6 ~?= (trees4,""),
    TestLabel "Some trees plus some rest" $ readTrees (str4 ++ "###") ~?= (trees2,"###"),
    TestLabel "Some trees plus some rest" $ readTrees (str4 ++ "   ###") ~?= (trees2,"   ###")
    ]

hunit_Read_TTree_readsPrec_test =
  let
    str1 = ""
    str2 = "{}"
    str3 = "_"
    str4 = "?"
    str5 = "###"
    str6 = "{a:A}"
    tree1 = (TNode (mkCId "a") (Fun (mkCId "A") []) [])
    str7 = "{a:A"
    str8 = "a:A}"
    str9 = "a:A"
    str10 = "{f:(A -> B -> A) {a:A} {b:B}}"
    tree2 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
      [
        (TNode (mkCId "a") (Fun (mkCId "A") []) []),
        (TNode (mkCId "b") (Fun (mkCId "B") []) [])
      ]
    str11 = "{f:(A -> A) {f:(A -> A) {f:(A -> A) {f:(A -> A) {a:A}}}}}"
    tree3 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A")])
      [
        TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A")])
        [
          TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A")])
          [
            TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A")])
            [
              TNode (mkCId "a") (Fun (mkCId "A") []) []
            ]
          ]
        ]
      ]
    str12 = "?A"
    str13 = "{?A}"
    tree4 = TMeta (mkCId "A")
    str14 = "{f:(A -> B -> A) {?A} {?B}}"
    tree5 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
      [
        (TMeta (mkCId "A")),
        (TMeta (mkCId "B"))
      ]
  in
    TestList [
    TestLabel "Empty String" $ (readsPrec 0 str1 :: [(TTree,String)])~?= [],
    TestLabel "Curly Brackets" $ (readsPrec 0 str2 :: [(TTree,String)])~?= [],
    TestLabel "Wildcard" $ (readsPrec 0 str3 :: [(TTree,String)])~?= [],
    TestLabel "Questionmark" $ (readsPrec 0 str3 :: [(TTree,String)])~?= [],
    TestLabel "Three hashes" $ (readsPrec 0 str5 :: [(TTree,String)])~?= [],
    TestLabel "Simple Tree" $ readsPrec 0 str6 ~?= [(tree1,"")],
    TestLabel "Partial Simple Tree 1" $ readsPrec 0 str7 ~?= [(tree1,"")],
    TestLabel "Partial Simple Tree 2" $ readsPrec 0 str8 ~?= [(tree1,"")],
    TestLabel "Partial Simple Tree 3" $ readsPrec 0 str9 ~?= [(tree1,"")],
    TestLabel "More complex Tree" $ readsPrec 0 str10 ~?= [(tree2,"")],
    TestLabel "Complex Tree" $ readsPrec 0 str11 ~?= [(tree3,"")],
    TestLabel "Meta Tree 1" $ readsPrec 0 str12 ~?= [(tree4,"")],
    TestLabel "Meta Tree 2" $ readsPrec 0 str13 ~?= [(tree4,"")],
    TestLabel "More complex Meta Tree" $ readsPrec 0 str14 ~?= [(tree5,"")],
    TestLabel "More complex Tree plus Extra 1" $ readsPrec 0 (str10 ++ "###") ~?= [(tree2,"###")],
    TestLabel "More complex Tree plus Extra 2" $ readsPrec 0 (str10 ++ "   ###") ~?= [(tree2,"   ###")]
    ]

hunit_listReplace_test = 
   let
     list1 = []
     list2 = ['a','a','b']
     list3 = ['a','a','a']
   in
     TestList [
     TestLabel "Empty List Positive Index" $ listReplace list1 2 'a' ~?= list1,
     TestLabel "Empty List Negative Index" $ listReplace list1 (-2) 'a' ~?= list1,
     TestLabel "Simple List Valid Index" $ listReplace list2 2 'a' ~?= list3,
     TestLabel "Simple List Negative Index" $ listReplace list2 (-2) 'a' ~?= list2,
     TestLabel "Simple List Index out of range" $ listReplace list2 3 'a' ~?= list2
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
    TestLabel "Empty List" $ powerList list1 ~?= list2,
    TestLabel "One Element" $ powerList list3 ~?= list4,
    TestLabel "Three Elements" $ powerList list5 ~?= list6
    ]

hunit_isMeta_test =
  let
    tree1 = TMeta (mkCId "A")
    tree2 = TMeta wildCId
    tree3 = TNode (mkCId "a") NoType []
    tree4 = TNode (mkCId "a") (Fun (mkCId "A") []) []
    tree5 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TMeta (mkCId "A")),(TMeta (mkCId "B"))]
  in
    TestList [
    TestLabel "Meta" $ isMeta tree1 ~?= True,
    TestLabel "Meta with wildcard" $ isMeta tree2 ~?= True,
    TestLabel "Simple Tree without type" $ isMeta tree3 ~?= False,
    TestLabel "Simple tree" $ isMeta tree4 ~?= False,
    TestLabel "Tree" $ isMeta tree5 ~?= False
    ]

hunit_getTreeCat_test =
  let
    tree1 = TMeta (mkCId "A")
    cat1 = mkCId "A"
    tree2 = TMeta wildCId
    cat2 = wildCId
    tree3 = TNode (mkCId "a") NoType []
    cat3 = wildCId
    tree4 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TMeta (mkCId "A")),(TMeta (mkCId "B"))]
  in
    TestList [
    TestLabel "Meta" $ getTreeCat tree1 ~?= cat1,
    TestLabel "Meta with wildcard" $ getTreeCat tree2 ~?= cat2,
    TestLabel "Simple Tree without type" $ getTreeCat tree3 ~?= cat3,
    TestLabel "Tree" $ getTreeCat tree4 ~?= cat1
    ]

hunit_gfAbsTreeToTTree_test =
  let
    pgf = readPGF "gf/ABCAbs.pgf"
    gtree1 = (EFun (mkCId "a"))
    ttree1 = TNode (mkCId "a") (Fun (mkCId "A") []) []
    gtree2 = (EFun wildCId)
    ttree2 = TNode wildCId NoType []
    gtree3 = (EApp (EApp (EFun (mkCId "f")) (EFun (mkCId "a"))) (EFun (mkCId "b")))
    ttree3 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
      [
        (TNode (mkCId "a") (Fun (mkCId "A") []) []),
        (TNode (mkCId "b") (Fun (mkCId "B") []) [])
      ]
    gtree4 = (EApp (EApp (EFun (mkCId "f")) (EFun (mkCId "a"))) (EApp (EApp (EFun (mkCId "g")) (EFun (mkCId "b"))) (EFun (mkCId "c"))))
    ttree4 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
      [
        (TNode (mkCId "a") (Fun (mkCId "A") []) []),
        (TNode (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")])
         [
           (TNode (mkCId "b") (Fun (mkCId "B") []) []),
           (TNode (mkCId "c") (Fun (mkCId "C") []) [])
         ])
      ]
    gtree5 = (ELit (LStr "Foo"))
    ttree5 = TMeta wildCId
  in
    TestList [
    TestLabel "EFun" $ TestCase $ pgf >>= (\p -> gfAbsTreeToTTree p gtree1 @?= ttree1),
    TestLabel "EFun with wildcard" $ TestCase $ pgf >>= (\p -> gfAbsTreeToTTree p gtree2 @?= ttree2),
    TestLabel "EApp 1" $ TestCase $ pgf >>= (\p -> gfAbsTreeToTTree p gtree3 @?= ttree3),
    TestLabel "EApp2 " $ TestCase $ pgf >>= (\p -> gfAbsTreeToTTree p gtree4 @?= ttree4),
    TestLabel "ELit" $ TestCase $ pgf >>= (\p -> gfAbsTreeToTTree p gtree5 @?= ttree5)
    ]

hunit_ttreeToGFAbsTree_test = 
  let
    ttree1 = TNode (mkCId "a") (Fun (mkCId "A") []) []
    gtree1 = (EFun (mkCId "a"))
    ttree2 = TNode wildCId NoType []
    gtree2 = (EFun wildCId)
    ttree3 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
      [
        (TNode (mkCId "a") (Fun (mkCId "A") []) []),
        (TNode (mkCId "b") (Fun (mkCId "B") []) [])
      ]
    gtree3 = (EApp (EApp (EFun (mkCId "f")) (EFun (mkCId "a"))) (EFun (mkCId "b")))
    ttree4 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
      [
        (TNode (mkCId "a") (Fun (mkCId "A") []) []),
        (TNode (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")])
         [
           (TNode (mkCId "b") (Fun (mkCId "B") []) []),
           (TNode (mkCId "c") (Fun (mkCId "C") []) [])
         ])
      ]
    gtree4 = (EApp (EApp (EFun (mkCId "f")) (EFun (mkCId "a"))) (EApp (EApp (EFun (mkCId "g")) (EFun (mkCId "b"))) (EFun (mkCId "c"))))
    ttree5 = TMeta wildCId
    gtree5 = (EMeta 0)
    ttree6 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
      [
        (TMeta (mkCId "A")),
        (TMeta (mkCId "B"))
      ]
    gtree6 = (EApp (EApp (EFun (mkCId "f")) (EMeta 0)) (EMeta 1))
  in
    TestList [
    TestLabel "Simple Tree" $ ttreeToGFAbsTree ttree1 ~=? gtree1,
    TestLabel "Simple Tree with wildcard and without type" $ ttreeToGFAbsTree ttree2 ~=? gtree2,
    TestLabel "More complex Tree" $ ttreeToGFAbsTree ttree3 ~=? gtree3,
    TestLabel "More complex Tree" $ ttreeToGFAbsTree ttree4 ~=? gtree4,
    TestLabel "Meta" $ ttreeToGFAbsTree ttree5 ~=? gtree5,
    TestLabel "More Meta" $ ttreeToGFAbsTree ttree6 ~=? gtree6
    ]

hunit_ttreeToLTree_test =
  let
    ttree1 = TMeta (mkCId "A")
    ltree1 = LNode (mkCId "A") 1 [LNode wildCId 0 [LLeaf]]
    ttree2 = TMeta wildCId
    ltree2 = LNode wildCId 1 [LNode wildCId 0 [LLeaf]]
    ttree3 = TNode (mkCId "a") (Fun (mkCId "A") []) []
    ltree3 = LNode (mkCId "A") 0 []
    ttree4 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
      [
        (TMeta (mkCId "A")),
        (TMeta (mkCId "B"))
      ]
    ltree4 = LNode (mkCId "A") 4 [LNode (mkCId "A") 1 [LNode wildCId 0 [LLeaf]],LNode (mkCId "B") 3 [LNode wildCId 2 [LLeaf]]]
    ttree5 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
      [
        (TNode (mkCId "a") (Fun (mkCId "A") []) []),
        (TNode (mkCId "b") (Fun (mkCId "B") []) [])
      ]
    ltree5 = LNode (mkCId "A") 2 [LNode (mkCId "A") 0 [],LNode (mkCId "B") 1 []]
  in
    TestList [
    TestLabel "Meta" $ ttreeToLTree ttree1 ~?= ltree1,
    TestLabel "Meta with wildcard" $ ttreeToLTree ttree2 ~?= ltree2,
    TestLabel "Simple Tree" $ ttreeToLTree ttree3 ~?= ltree3,
    TestLabel "Tree with Metas" $ ttreeToLTree ttree4 ~?= ltree4,
    TestLabel "Tree" $ ttreeToLTree ttree5 ~?= ltree5
    ]
  
hunit_maxDepth_test =
  let
    tree1 = TMeta (mkCId "A")
    tree2 = TMeta wildCId
    tree3 = TNode (mkCId "a") NoType []
    tree4 = TNode (mkCId "f") (Fun (mkCId "E") [(mkCId "A"),(mkCId "B"),(mkCId "C"),(mkCId "D")])
      [
        (TMeta (mkCId "A")),
        (TNode (mkCId "b") (Fun (mkCId "B") []) []),
        (TNode (mkCId "g") (Fun (mkCId "C") [(mkCId "C"),(mkCId "B")])
         [
           (TNode (mkCId "c") (Fun (mkCId "C") []) []),
           (TNode (mkCId "h") (Fun (mkCId "B") [(mkCId "B")])
            [
              (TNode (mkCId "h") (Fun (mkCId "B") [(mkCId "B")])
               [
                 (TNode (mkCId "b") (Fun (mkCId "B") []) [])
               ])
            ])
         ]),
        (TNode (mkCId "i") (Fun (mkCId "D") [(mkCId "D")])
         [
           (TNode (mkCId "i") (Fun (mkCId "D") [(mkCId "D")]) [])
         ]
        )
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
    tree1 = TMeta (mkCId "A")
    tree2 = TMeta wildCId
    tree3 = TNode (mkCId "a") NoType []
    tree4 = TNode (mkCId "f") (Fun (mkCId "E") [(mkCId "A"),(mkCId "B"),(mkCId "C"),(mkCId "D")])
      [
        (TMeta (mkCId "A")),
        (TNode (mkCId "b") (Fun (mkCId "B") []) []),
        (TNode (mkCId "g") (Fun (mkCId "C") [(mkCId "C"),(mkCId "B")])
         [
           (TNode (mkCId "c") (Fun (mkCId "C") []) []),
           (TNode (mkCId "h") (Fun (mkCId "B") [(mkCId "B")])
            [
              (TNode (mkCId "h") (Fun (mkCId "B") [(mkCId "B")])
               [
                 (TNode (mkCId "b") (Fun (mkCId "B") []) [])
               ])
            ])
         ]),
        (TNode (mkCId "i") (Fun (mkCId "D") [(mkCId "D")])
         [
           (TNode (mkCId "i") (Fun (mkCId "D") [(mkCId "D")]) [])
         ]
        )
      ]
  in
    TestList [
    TestLabel "Meta" $ countNodes tree1 ~?= 0,
    TestLabel "Meta with wildcard" $ countNodes tree2 ~?= 0,
    TestLabel "Simple tree without type" $ countNodes tree3 ~?= 1,
    TestLabel "Complex tree" $ countNodes tree4 ~?= 9
             ]

hunit_makeMeta_test =
  let
    ttree1 = TMeta (mkCId "A")
    mtree1 = MetaTTree (TMeta (mkCId "A")) empty
    ttree2 = TNode (mkCId "a") (Fun (mkCId "A") []) []
    mtree2 = MetaTTree (TNode (mkCId "a") (Fun (mkCId "A") []) []) empty
    in
    TestList [
    TestLabel "Meta" $ makeMeta ttree1 ~?= mtree1,
    TestLabel "Simple Tree" $ makeMeta ttree2 ~?= mtree2
    ]

hunit_replaceBranch_test = 
  let
    new = TMeta wildCId
    tree1 = TMeta (mkCId "A")
    tree2 = TNode (mkCId "f") NoType []
    tree3 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B"),(mkCId "C"),(mkCId "D")])
      [
        (TNode (mkCId "a") (Fun (mkCId "A") []) []),
        (TMeta (mkCId "B")),
        (TNode (mkCId "g") (Fun (mkCId "C") [(mkCId "C")]) [(TMeta (mkCId "C"))]),
        (TNode (mkCId "d") (Fun (mkCId "D") []) [])
      ]
  in
    TestList [
    TestLabel "Meta" $ replaceBranch tree1 0 new ~?= tree1,    
    TestLabel "Meta negative index" $ replaceBranch tree1 (-1) new ~?= tree1,
    TestLabel "Meta index out of range" $ replaceBranch tree1 1 new ~?= tree1,
    TestLabel "Simple Tree without type" $ replaceBranch tree2 0 new ~?= tree2,
    TestLabel "Simple Tree without type and negative index" $ replaceBranch tree2 (-1) new ~?= tree2,
    TestLabel "Simple Tree without type and index out of range" $ replaceBranch tree2 1 new ~?= tree2,
    TestLabel "Tree" $ selectBranch (replaceBranch tree3 0 new) 0 ~?= Just new,
    TestLabel "Tree" $ selectBranch (replaceBranch tree3 1 new) 1 ~?= Just new,
    TestLabel "Tree" $ selectBranch (replaceBranch tree3 2 new) 2 ~?= Just new,
    TestLabel "Tree" $ selectBranch (replaceBranch tree3 3 new) 3 ~?= Just new,
    TestLabel "Tree negative index" $ replaceBranch tree3 (-1) new ~?= tree3,
    TestLabel "Tree index out of range" $ replaceBranch tree3 5 new ~?= tree3
    ]

hunit_replaceNode_test =
  let
    new = TMeta wildCId
    tree1 = TMeta (mkCId "A")
    tree2 = TNode (mkCId "f") NoType []
    tree3 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B"),(mkCId "C"),(mkCId "D")])
      [
        (TNode (mkCId "a") (Fun (mkCId "A") []) []),
        (TMeta (mkCId "B")),
        (TNode (mkCId "g") (Fun (mkCId "C") [(mkCId "C")]) [(TMeta (mkCId "C"))]),
        (TNode (mkCId "d") (Fun (mkCId "D") []) [])
      ]
  in
    TestList [
    TestLabel "Meta empty path" $ replaceNode tree1 [] new ~?= new,
    TestLabel "Meta path too long" $ replaceNode tree1 [0] new ~?= tree1,
    TestLabel "Simple tree empty path" $ replaceNode tree2 [] new ~?= new,
    TestLabel "Simple tree path too long" $ replaceNode tree2 [0] new ~?= tree2,
    TestLabel "Tree empty path" $ replaceNode tree3 [] new ~?= new,
    TestLabel "Tree 1" $ selectNode (replaceNode tree3 [0] new) [0] ~?= Just new,
    TestLabel "Tree 2" $ selectNode (replaceNode tree3 [1] new) [1] ~?= Just new,
    TestLabel "Tree 3" $ selectNode (replaceNode tree3 [2] new) [2] ~?= Just new,
    TestLabel "Tree 2" $ selectNode (replaceNode tree3 [2,0] new) [2,0] ~?= Just new,
    TestLabel "Tree 2" $ selectNode (replaceNode tree3 [3] new) [3] ~?= Just new,
    TestLabel "Tree negative path" $ replaceNode tree3 [-1] new ~?= tree3,
    TestLabel "Tree path out of range" $ replaceNode tree3 [4] new ~?= tree3
    
    ]

hunit_replaceNodeByMeta_test = -- TODO
    TestList [
    ]

hunit_maxPath_test =
  let
    tree1 = TMeta (mkCId "A")
    tree2 = TMeta wildCId
    tree3 = TNode (mkCId "a") NoType []
    tree4 = TNode (mkCId "f") (Fun (mkCId "E") [(mkCId "A"),(mkCId "B"),(mkCId "C"),(mkCId "D")])
      [
        (TMeta (mkCId "A")),
        (TNode (mkCId "b") (Fun (mkCId "B") []) []),
        (TNode (mkCId "g") (Fun (mkCId "C") [(mkCId "C"),(mkCId "B")])
         [
           (TNode (mkCId "c") (Fun (mkCId "C") []) []),
           (TNode (mkCId "h") (Fun (mkCId "B") [(mkCId "B")])
            [
              (TNode (mkCId "h") (Fun (mkCId "B") [(mkCId "B")])
               [
                 (TNode (mkCId "b") (Fun (mkCId "B") []) [])
               ])
            ])
         ]),
        (TNode (mkCId "i") (Fun (mkCId "D") [(mkCId "D")])
         [
           (TNode (mkCId "i") (Fun (mkCId "D") [(mkCId "D")]) [])
         ]
        )
      ]
  in
    TestList [
    TestLabel "Meta" $ maxPath 3 tree1 ~?= [[]],
    TestLabel "Meta with wildcard" $ maxPath 3 tree2 ~?= [[]],
    TestLabel "Simple tree without type" $ maxPath 3 tree3 ~?= [[]],
    TestLabel "Complex tree 1" $ maxPath 2 tree4 ~?= [[2,0],[2,1],[3,0]],
    TestLabel "Complex tree 2" $ maxPath 9 tree4 ~?= [[2,1,0,0]]
    ]

hunit_findPaths_test =
  let
    tree1 = TMeta (mkCId "A")
    tree2 = TMeta wildCId
    tree3 = TNode (mkCId "a") NoType []
    tree4 = TNode (mkCId "f") (Fun (mkCId "E") [(mkCId "A"),(mkCId "B"),(mkCId "C"),(mkCId "D")])
      [
        (TMeta (mkCId "A")),
        (TNode (mkCId "b") (Fun (mkCId "B") []) []),
        (TNode (mkCId "g") (Fun (mkCId "C") [(mkCId "C"),(mkCId "B")])
         [
           (TNode (mkCId "c") (Fun (mkCId "C") []) []),
           (TNode (mkCId "h") (Fun (mkCId "B") [(mkCId "B")])
            [
              (TNode (mkCId "h") (Fun (mkCId "B") [(mkCId "B")])
               [
                 (TNode (mkCId "b") (Fun (mkCId "B") []) [])
               ])
            ])
         ]),
        (TNode (mkCId "i") (Fun (mkCId "D") [(mkCId "D")])
         [
           (TNode (mkCId "i") (Fun (mkCId "D") [(mkCId "D")]) [])
         ]
        )
      ]
  in
    TestList [
    TestLabel "Meta" $ findPaths 3 tree1 ~?= [[]],
    TestLabel "Meta with wildcard" $ findPaths 3 tree2 ~?= [[]],
    TestLabel "Simple tree without type" $ findPaths 3 tree3 ~?= [[]],
    TestLabel "Complex tree 1" $ findPaths 2 tree4 ~?= [[1],[2,0],[2,1],[3,0]],
    TestLabel "Complex tree 2" $ findPaths 9 tree4 ~?= [[1],[2,0],[2,1,0,0],[3,0]]
    ]

hunit_prune_test = -- TODO
  let
    tree1 = (read "{f:(A -> B -> A) {a:A} {g:B {b:B} {c:C}}}") :: TTree
    mtrees1 = fromList $ [
      (MetaTTree (read "{?A}") $ fromList [([], read "{f:(A -> B -> A) {a:A} {g:B {b:B} {c:C}}}")]),
      (MetaTTree (read "{f:(A -> B -> A) {?A} {?B}}") $ fromList [([0], read "{a:A}"), ([1], read "{g:(B -> C -> B) {b:B} {c:C}}")]),
      (MetaTTree (read "{f:(A -> B -> A) {a:A} {?B}}") $ fromList [([1], read "{g:(B -> C -> B) {b:B} {c:C}}")]),
      (MetaTTree (read "{f:(A -> B -> A) {?A} {g:(B -> C -> B) {?B} {?C}}}") $ fromList [([0], read "{a:A}"), ([1,0], read "{b:B}"), ([1,1], read "{c:C}")]),
      (MetaTTree (read "{f:(A -> B -> A) {?A} {g:(B -> C -> B) {b:B} {?C}}}") $ fromList [([0], read "{a:A}"), ([1,1], read "{c:C}")]),
      (MetaTTree (read "{f:(A -> B -> A) {?A} {g:(B -> C -> B) {?B} {c:C}}}") $ fromList [([0], read "{a:A}"), ([1,0], read "{b:B}")]),
      (MetaTTree (read "{f:(A -> B -> A) {?A} {g:(B -> C -> B) {b:B} {c:C}}}") $ fromList [([0], read "{a:A}")]),
      (MetaTTree (read "{f:(A -> B -> A) {a:A} {g:(B -> C -> B) {?B} {?C}}}") $ fromList [([1,0], read "{b:B}"), ([1,1], read "{c:C}")]),
      (MetaTTree (read "{f:(A -> B -> A) {a:A} {g:(B -> C -> B) {b:B} {?C}}}") $ fromList [([1,1], read "{c:C}")]),
      (MetaTTree (read "{f:(A -> B -> A) {a:A} {g:(B -> C -> B) {?B} {c:C}}}") $ fromList [([1,0], read "{b:B}")]),
      (MetaTTree (read "{f:(A -> B -> A) {a:A} {g:(B -> C -> B) {b:B} {c:C}}}") empty)
      ]
  in
    TestList [
    -- prune {{f:A {a:A} {g:B {b:B} {c:C}}}} 2
    -- [({?A}, [([], {{f:A {a:A} {g:B {b:B} {c:C}}}})]),
    --  ({{f:A ?A ?B}}, [([0], {{a:A}}), ([1], {{g:B {b:B} {c:C}}})]),
    --  ({{f:A {a:A} ?B}}, [([1], {{g:B {b:B} {c:C}}})]),
    --  ({{f:A ?A {g:B ?B ?C}}}, [([0], {{a:A}}), ([1,0], {{b:B}}), ([1,1], {{c:C}})]),
    --  ({{f:A {a:A} {g:B ?B ?C}}}, [([1,0], {{b:B}}), ([1,1], {{c:C}})]),
    --  ]
    TestLabel "Peters Example" $ prune tree1 2 ~?= mtrees1
    ]

hunit_getMetaLeaveCats_test =
  let
    tree1 = TMeta (mkCId "A")
    tree2 = TNode (mkCId "a") (Fun (mkCId "A") []) []
    tree3 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
      [
        (TMeta (mkCId "A")),
        (TMeta wildCId)
      ]
    tree4 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "A")])
      [
        (TMeta (mkCId "A")),
        (TMeta (mkCId "A"))
      ]
    tree5 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
      [
        TNode (mkCId "g") (Fun (mkCId "A") [(mkCId "A")])
        [
          TNode (mkCId "g") (Fun (mkCId "A") [(mkCId "A")])
          [
            TNode (mkCId "g") (Fun (mkCId "A") [(mkCId "A")])
            [
              (TMeta (mkCId "A"))

            ]
          ]
        ],
        (TMeta (mkCId "B"))
      ]
  in
    TestList [
    TestLabel "Meta" $ getMetaLeaveCats tree1 ~?= fromList [(mkCId "A")],
    TestLabel "Simple tree without metas" $ getMetaLeaveCats tree2 ~?= empty,
    TestLabel "Simple tree 1" $ getMetaLeaveCats tree3 ~?= fromList [(mkCId "A"),wildCId],
    TestLabel "Simple tree 2" $ getMetaLeaveCats tree4 ~?= fromList [(mkCId "A")],
    TestLabel "Tree" $ getMetaLeaveCats tree5 ~?= fromList [(mkCId "A"),(mkCId "B")]
    ]

hunit_getMetaPaths_test = 
  let
    tree1 = TMeta (mkCId "A")
    tree2 = TNode (mkCId "a") (Fun (mkCId "A") []) []
    tree3 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
      [
        (TMeta (mkCId "A")),
        (TMeta wildCId)
      ]
    tree4 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "A")])
      [
        (TMeta (mkCId "A")),
        (TMeta (mkCId "A"))
      ]
    tree5 = TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
      [
        TNode (mkCId "g") (Fun (mkCId "A") [(mkCId "A")])
        [
          TNode (mkCId "g") (Fun (mkCId "A") [(mkCId "A")])
          [
            TNode (mkCId "g") (Fun (mkCId "A") [(mkCId "A")])
            [
              (TMeta (mkCId "A"))

            ]
          ]
        ],
        (TMeta (mkCId "B"))
      ]
  in
    TestList [
    TestLabel "Meta" $ getMetaPaths tree1 ~?= [([],(mkCId "A"))],
    TestLabel "Simple tree without metas" $ getMetaPaths tree2 ~?= [],
    TestLabel "Simple tree" $ getMetaPaths tree3 ~?= [([0],(mkCId "A")),([1],wildCId)],
    TestLabel "Simple tree" $ getMetaPaths tree4 ~?= [([0],(mkCId "A")),([1],(mkCId "A"))],
    TestLabel "Tree" $ getMetaPaths tree5 ~?= [([0,0,0,0],(mkCId "A")),([1],(mkCId "B"))]
    ]

hunit_applyRule_test = -- TODO
  TestList [
           ]

hunit_combine_test = -- TODO
  TestList [
           ]

hunit_extendTree_test = -- TODO
  TestList [
           ]

hunit_generate_test = -- TODO
  let
    grammar =
      Grammar
      (mkCId "A")
      [
        (Function (mkCId "f") (Fun (mkCId "A") [(mkCId "A"), (mkCId "B")])),
        (Function (mkCId "g") (Fun (mkCId "B") [(mkCId "B"), (mkCId "C")])),
        (Function (mkCId "a") (Fun (mkCId "A") [])),
        (Function (mkCId "b") (Fun (mkCId "B") [])),
        (Function (mkCId "c") (Fun (mkCId "C") []))
      ]
      emptyPGF
    result = fromList
      [
        (MetaTTree (read "{?A}") $ fromList [([], read "{?A}")]),
        (MetaTTree (read "{a:A}") empty),
        (MetaTTree (read "{f:A {?A} {?B}}") $ fromList [([0], read "{?A}"), ([1], read "{?B}")]),
        (MetaTTree (read "{f:A {a:A} {?B}}") $ fromList [([1], read "{?B}")]),
        (MetaTTree (read "{f:A {f:A {?A} {?B}} {?B}}") $ fromList [([0,0], read "{?A}"), ([0,1], read "{?B}"), ([1], read "{?B}")]),
        (MetaTTree (read "{f:A {?A} {b:B}") $ fromList [([0], read "{?A}")]),
        (MetaTTree (read "{f:A {?A} {g:B {?B} {?C}}}") $ fromList [([0], read "{?A}"),([1,0], read "{?B}"),([1,1], read "{?C}")]),
        (MetaTTree (read "{f:A {a:A} {b:B}}") empty),
        (MetaTTree (read "{f:A {a:A} {g:B {?B} {?C}}}") $ fromList [([1,0], read "{?B}"),([1,1], read "{?C}")]),
        (MetaTTree (read "{f:A {f:A {?A} {?B}} {b:B}}") $ fromList [([0,0], read "{?A}"), ([0,1], read "{?B}")]),
        (MetaTTree (read "{f:A {f:A {?A} {?B}} {g:B {?B} {?C}}}") $ fromList [([0,0], read "{?A}"), ([0,1], read "{?B}"),([1,0], read "{?B}"), ([1,1], read "{?C}")])
      ]:: Set MetaTTree
  in
  TestList [
    TestLabel "Peters example" $ Muste.Tree.Internal.generate grammar (startcat grammar) 2 ~?= result
           ]

hunit_combineTrees_test = -- TODO
  TestList [
           ]

hunit_computeCosts_test = -- TODO
  TestList [
           ]

hunit_match_test = -- TODO
  TestList [
           ]
  
show_tests =
  TestList [
  TestLabel "Show TTree show" hunit_Show_TTree_show_test,
  TestLabel "Show MetaTTree show" hunit_Show_MetaTTree_show_test
  ]
  
read_tests =
  TestList [
  hunit_Read_TTree_readsPrec_test
  ]

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
  TestLabel "consumeChar" hunit_consumeChar_test,
  TestLabel "readFunType" hunit_readFunType_test,
  TestLabel "getChildCats" hunit_getChildCats_test,
  TestLabel "checkType" hunit_checkType_test,
  TestLabel "fixTypes" hunit_fixTypes_test,
  TestLabel "readTree" hunit_readTree_test,
  TestLabel "readTree" hunit_readTrees_test,
  TestLabel "isMeta" hunit_isMeta_test,
  TestLabel "getTreeCat" hunit_getTreeCat_test,
  TestLabel "gfAbsTreeToTTree" hunit_gfAbsTreeToTTree_test,
  TestLabel "gfAbsTreeToTTree" hunit_ttreeToGFAbsTree_test,
  TestLabel "ttreeToLTree" hunit_ttreeToLTree_test,
  TestLabel "maxDepth" hunit_maxDepth_test,
  TestLabel "countNodes" hunit_countNodes_test,
  TestLabel "makeMeta" hunit_makeMeta_test,
  TestLabel "replaceBranch" hunit_replaceBranch_test,
  TestLabel "replaceNode" hunit_replaceNode_test,
  TestLabel "replaceNodeByMeta" hunit_replaceNodeByMeta_test,
  TestLabel "maxPath" hunit_maxPath_test,
  TestLabel "findPaths" hunit_findPaths_test,
  TestLabel "prune" hunit_prune_test,
  TestLabel "getMetaLeaveCats" hunit_getMetaLeaveCats_test,
  TestLabel "getMetaPaths" hunit_getMetaPaths_test,
  TestLabel "applyRule" hunit_applyRule_test,
  TestLabel "combine" hunit_combine_test,
  TestLabel "extendTree" hunit_extendTree_test,
  TestLabel "generate" hunit_generate_test,
  TestLabel "computeCosts" hunit_computeCosts_test,
  TestLabel "combineTrees" hunit_combineTrees_test,
  TestLabel "match" hunit_match_test
  ]

list_function_tests =
  TestList [
  TestLabel "ListReplace" hunit_listReplace_test,
  TestLabel "powerList" hunit_powerList_test
  ]
  
hunit_tests = TestList [treec_tests, show_tests, read_tests, tree_function_tests, list_function_tests]
    
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

-- Conversion between GFAbsTrees and TTrees
quickcheck_tests = [ ("Meta1",prop_metaTest) ]

