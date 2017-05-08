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
import Data.List (sort)
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

hunit_hasMetas_test =
  let
    -- tree1 in Data.hs
    tree2 = TMeta wildCard
    tree3 = TNode "a" NoType []
    tree4 = TNode "a" (Fun "A" []) []
    tree5 = TNode "f" (Fun "A" ["A","B"]) [TMeta "A",TMeta "B"]
  in
    TestList [
    TestLabel "Meta" ( hasMetas tree1 ~?= True ),
    TestLabel "Meta with wildcard" ( hasMetas tree2 ~?= True ),
    TestLabel "Simple Tree without type" ( hasMetas tree3 ~?= False ),
    TestLabel "Simple tree" ( hasMetas tree4 ~?= False ),
    TestLabel "Tree" ( hasMetas tree5 ~?= True )
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

hunit_extendTreeToSet_test = 
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
    TestLabel "Empty grammar depth 0" ( extendTreeToSet grammar1 tree1 0 ~?= empty ),
    TestLabel "Empty grammar depth 1" ( extendTreeToSet grammar1 tree1 1 ~?= empty  ),
    TestLabel "Grammar without rules depth 0" ( extendTreeToSet grammar2 tree1 0 ~?= empty ),
    TestLabel "Grammar without rules depth 1" ( extendTreeToSet grammar2 tree1 0 ~?= empty ),
    TestLabel "Simple Grammar 3 tree 1 depth 0" ( extendTreeToSet grammar3 tree1 0 ~?= singleton tree1 ),
    TestLabel "Simple Grammar 3 tree 1 depth 1" ( extendTreeToSet grammar3 tree1 1 ~?= fromList [tree1,tree2] ),
    TestLabel "Simple Grammar 3 tree 1 depth 2" ( extendTreeToSet grammar3 tree1 2 ~?= fromList [tree1,tree2] ),
    TestLabel "Simple Grammar 3 tree 1 depth 3" ( extendTreeToSet grammar3 tree1 3 ~?= fromList [tree1,tree2] ),
    TestLabel "Simple Grammar 4 tree 1 depth 0" ( extendTreeToSet grammar4 tree1 0 ~?= singleton tree1 ),
    TestLabel "Simple Grammar 4 tree 1 depth 1" ( extendTreeToSet grammar4 tree1 1 ~?= fromList [tree1,tree2,tree3,tree4,tree5] ),
    TestLabel "Simple Grammar 4 tree 1 depth 2" ( extendTreeToSet grammar4 tree1 2 ~?= fromList [tree1,tree2,tree3,tree4,tree5] ),
    TestLabel "Simple Grammar 4 tree 1 depth 3" ( extendTreeToSet grammar4 tree1 3 ~?= fromList [tree1,tree2,tree3,tree4,tree5] ),
    TestLabel "Simple Grammar 3 tree 7 depth 0" ( extendTreeToSet grammar3 tree7 0 ~?= singleton tree7 ),
    TestLabel "Simple Grammar 3 tree 7 depth 1" ( extendTreeToSet grammar3 tree7 1 ~?= singleton tree7 ),
    TestLabel "Simple Grammar 3 tree 7 depth 2" ( extendTreeToSet grammar3 tree7 2 ~?= fromList [tree7,tree8] ),
    TestLabel "Simple Grammar 3 tree 7 depth 3" ( extendTreeToSet grammar3 tree7 3 ~?= fromList [tree7,tree8,tree9,tree10] ),
    TestLabel "Simple Grammar 3 tree 7 depth 4" ( extendTreeToSet grammar3 tree7 4 ~?= fromList [tree7,tree8,tree9,tree10] )
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
  TestLabel "getChildCats" hunit_getChildCats_test,
  TestLabel "isMeta" hunit_isMeta_test,
  TestLabel "hasMetas" hunit_hasMetas_test,
  TestLabel "getTreeCat" hunit_getTreeCat_test,
  TestLabel "gfAbsTreeToTTreeWithPGF" hunit_gfAbsTreeToTTreeWithPGF_test,
  TestLabel "gfAbsTreeToTTreeWithGrammar" hunit_gfAbsTreeToTTreeWithGrammar_test,
  TestLabel "ttreeTogfAbsTree" hunit_ttreeToGFAbsTree_test,
  TestLabel "ttreeToLTree" hunit_ttreeToLTree_test,
  TestLabel "getPath" hunit_getPath_test,
  TestLabel "maxDepth" hunit_maxDepth_test,
  TestLabel "replaceBranch" hunit_replaceBranch_test,
  TestLabel "replaceNode" hunit_replaceNode_test,
  TestLabel "getMetaLeafCatsSet" hunit_getMetaLeafCatsSet_test,
  TestLabel "getMetaLeafCatsSet"  hunit_getMetaLeafCatsList_test,
  TestLabel "getMetaPaths" hunit_getMetaPaths_test,
  TestLabel "applyRule" hunit_applyRule_test,
  TestLabel "combineToSet" hunit_combineToSet_test,
  TestLabel "combineToList" hunit_combineToList_test,
  TestLabel "extendTreeToSet" hunit_extendTreeToSet_test
--  TestLabel "extendTreeToSet" hunit_extendTreeToList_test -- TODO
--  TestLabel "generate" hunit_generate_test, -- TODO
  ]

list_function_tests =
  TestList [
  TestLabel "ListReplace" hunit_listReplace_test,
  TestLabel "powerList" hunit_powerList_test
  ]
  
hunit_tests = TestList [
  treec_tests,
  tree_function_tests,
  list_function_tests
  ]

prop_generatedTTreeIsNotMeta :: TTree -> Bool
prop_generatedTTreeIsNotMeta = not . isMeta

-- prop_gfAbsTreeToTTreeIdentity -- TODO

prop_combineIdentity :: TTree -> Rule -> Int -> Bool
prop_combineIdentity t r d =
  combineToSet t d r == (fromList $ combineToList t d r)
  
prop_treeConversionIdentity :: Grammar -> TTree -> Gen Property
prop_treeConversionIdentity g tree =
  let
    compatible grammar (TNode id typ ts) =
      elem (Function id typ) (getAllRules g) && (and $ map (compatible grammar) ts)
  in
    do
      --    tree <- arbitraryTTree g 5
      return $ compatible g tree ==> ((gfAbsTreeToTTreeWithGrammar g . ttreeToGFAbsTree) tree) == tree

-- prop_getMetaLeafCatsIdentity -- TODO

-- | Finds paths for all meta nodes
prop_metaPathsForAllMetaCats :: TTree -> Bool
prop_metaPathsForAllMetaCats tree =
  getMetaLeafCatsSet tree == fromList (map snd (getMetaPaths tree))

-- | Meta paths not empty when tree has meta nodes
-- prop_metasHaveMetaPaths -- TODO


-- Conversion between GFAbsTrees and TTrees
quickcheck_tests :: [(TestName,Property)]
quickcheck_tests = [
  ("Generated ttrees are not Metas",property prop_generatedTTreeIsNotMeta),
  ("Tree conversion identity", property prop_treeConversionIdentity),
  ("Combine identity", property prop_combineIdentity),
  ("Meta paths 1",property prop_metaPathsForAllMetaCats)
--  ("Meta paths 2",property prop_metasHaveMetaPaths)  -- Fails because there are no metas
  ]

