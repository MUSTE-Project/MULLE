import Test.QuickCheck
import PGF
import Tree
import Grammar
import Data.List
import Test.HUnit.Text
import Test.HUnit.Base
    
-- HUnit tests
-- Basic tests
-- Test read
-- read equality Test 1
{-
  reads the tree as a string and compares with the data structure
  simple tree
-}
t1 = (TNode (mkCId "t1") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TNode (mkCId "a") (Fun (mkCId "A") []) []),(TNode (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")]) [(TNode (mkCId "b") (Fun (mkCId "B") []) []),(TNode (mkCId "c") (Fun (mkCId "C") []) [])])])
ts1 = "{t1:(A -> B -> A) {a:A} {g:(B -> C -> B) {b:B} {c:C}}}"
test_hu_read1 =
  do
    putStrLn "Check read equality Test 1"
    runTestTT (t1 ~?= (read ts1 :: TTree))

-- read equality Test 2
{-
  reads the tree as a string and compares with the data structure
  quite deep tree
-}
t2 = (TNode (mkCId "t2") (Fun (mkCId "F") [(mkCId "A"), (mkCId "G")]) [(TMeta (mkCId "A")), (TNode (mkCId "g") (Fun (mkCId "G") [(mkCId "B"), (mkCId "H")]) [(TMeta (mkCId "B")), (TNode (mkCId "h") (Fun (mkCId "H") [(mkCId "C"), (mkCId "I")]) [(TMeta (mkCId "C")), (TNode (mkCId "i") (Fun (mkCId "I") [(mkCId "D"),(mkCId "E")]) [(TMeta (mkCId "D")), (TMeta (mkCId "E"))])])])])
ts2 = "{t2:(A -> G -> F) {?A} {g:(B -> H -> G) {?B} {h:(C -> I -> H) {?C} {i:(D -> E -> I) {?D} {?E}}}}}"
test_hu_read2 =
  do
    putStrLn "Check read equality Test 2"
    runTestTT (t2 ~?= (read ts2 :: TTree))

-- read equality Test 3
{-
  reads the tree as a string and compares with the data structure
  all subtrees are metas
-}
t4 = (TNode (mkCId "t4") (Fun (mkCId "A") [(mkCId "A"),(mkCId "A")]) [(TMeta (mkCId "A")), (TMeta (mkCId "A"))])
ts4 = "{t4:(A -> A -> A) {?A} {?A}}"
test_hu_read3 =
  do
    putStrLn "Check read equality Test 3"
    runTestTT (t4 ~?= (read ts4 :: TTree))


t3 = let (MetaTTree (TNode _ typ trees) subTrees) = replaceNodeByMeta (replaceNodeByMeta (makeMeta t1) [1,0]) [1,1] in (MetaTTree (TNode (mkCId "t3") typ trees) subTrees)

g2 = Grammar (mkCId "A")
     [
      Function (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "A")]),
      Function (mkCId "a") (Fun (mkCId "A") []) -- ,
--      Function (mkCId "aa") (Fun (mkCId "A") [(mkCId "A")])
     ]

r1 = Function (mkCId "b") (Fun (mkCId "B") [])

r2 = Function (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")])

r3 = Function (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "A")])
     
mt11 =
  (MetaTTree
   (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"), (mkCId "B")])
    [
       (TMeta (mkCId "A")),
       (TMeta (mkCId "B"))
    ]
   )
   ([([0], (TNode (mkCId "a") (Fun (mkCId "A") []) [])),
     ([1], (TNode (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")])
            [
              (TNode (mkCId "b") (Fun (mkCId "B") []) []),
              (TNode (mkCId "c") (Fun (mkCId "C") []) [])
            ]
           )
     )
    ]
   )
  )
mt12 =
  (MetaTTree
   (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
    [
      (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
       [
         (TMeta (mkCId "A")),
         (TMeta (mkCId "B"))
       ]
      ),
      (TNode (mkCId "b") (Fun (mkCId "B") []) [])
    ]
   )
   [([0,0], (TMeta (mkCId "A"))),
    ([0,1], (TMeta (mkCId "B")))
   ]
  )
rt1 =
  (4,
   (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
    [
      (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
       [
         (TNode (mkCId "a") (Fun (mkCId "A") []) []),
         (TNode (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")])
          [
            (TNode (mkCId "b") (Fun (mkCId "B") []) []),
            (TNode (mkCId "c") (Fun (mkCId "C") []) [])
          ]
         )
       ]),
      (TNode (mkCId "b") (Fun (mkCId "B") []) [])
    ]
   )
  )
-- (the cost 1 is because the splitted_tree has 1 node, and 3 is because the generated_tree has 3 nodes)
-- Not working yet
mt21 =
  (MetaTTree
   (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"), (mkCId "B")])
    [
      (TMeta (mkCId "A")),
      (TMeta (mkCId "B"))
    ]
   )
   [
     ([0], (TNode (mkCId "a") (Fun (mkCId "A") []) [])),
     ([1], (TNode (mkCId "g") (Fun (mkCId "B") [(mkCId "B"), (mkCId "C")])
            [
              (TNode (mkCId "b") (Fun (mkCId "B") []) []),
              (TNode (mkCId "c") (Fun (mkCId "C") []) [])
            ]
           )
     )
   ]
  )
mt22 =
  (MetaTTree
   (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"), (mkCId "B")])
    [
      (TMeta (mkCId "A")),
      (TNode (mkCId "b") (Fun (mkCId "B") []) [])
    ]
   )
   [
     ([0], (TMeta (mkCId "A")))
   ]
  )
rt2 =
  (6,
   (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"), (mkCId "B")])
    [
      (TNode (mkCId "a") (Fun (mkCId "A") []) []),
      (TNode (mkCId "b") (Fun (mkCId "B") []) [])
    ]
   )
  )
-- (the cost 1 is because the splitted_tree has 1 node, and 2 is because the generated_tree has 2 nodes; the cost 3 is because the B tree was removed, and it has 3 nodes)

-- Must in haskell mail
-- prune {{f:A {a:A} {g:B {b:B} {c:C}}}} 2
-- ==> [({?A}, [([], {{f:A {a:A} {g:B {b:B} {c:C}}}})]),
--      ({{f:A ?A ?B}}, [([0], {{a:A}}), ([1], {{g:B {b:B} {c:C}}})]),
--      ({{f:A {a:A} ?B}}, [([1], {{g:B {b:B} {c:C}}})]),
--      ({{f:A ?A {g:B ?B ?C}}}, [([0], {{a:A}}), ([1,0], {{b:B}}), ([1,1], {{c:C}})]),
--      ({{f:A {a:A} {g:B ?B ?C}}}, [([1,0], {{b:B}}), ([1,1], {{c:C}})]),
--      ]
test_hu_prune =
    let
        tree :: TTree
        tree = read "{f:A {a:A} {g:B {b:B} {c:C}}}"
        result :: [MetaTTree]
        result = [(MetaTTree (read "{?A}" :: TTree) [([], read "{f:(A -> B -> A) {a:A} {g:B {b:B} {c:C}}}" :: TTree)]),
                  (MetaTTree (read "{f:(A -> B -> A) {?A} {?B}}") [([0], read "{a:A}"), ([1], read "{g:(B -> C -> B) {b:B} {c:C}}")]),
                  (MetaTTree (read "{f:(A -> B -> A) {a:A} ?B}") [([1], read "{g:(B -> C -> B) {b:B} {c:C}}")]),
                  (MetaTTree (read "{f:(A -> B -> A) {?A} {g:(B -> C -> B) {?B} {?C}}}") [([0], read "{a:A}"), ([1,0], read "{b:B}"), ([1,1], read "{c:C}")]),
                  (MetaTTree (read "{f:(A -> B -> A) {a:A} {g:(B -> C -> B) {?B} {?C}}}") [([1,0], read "{b:B}"), ([1,1], read "{c:C}")])
                 ]
    in
      putStrLn $ show (prune tree 2)
--      runTestTT (prune tree 2 ~?= result)
-- grammar = [("f", "A", ["A","B"]), ("g", "B", ["B","C"]),
--            ("a", "A", []), ("b", "B", []), ("c", "C", [])]
grammar = Grammar (mkCId "A")
     [
      Function (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]),
      Function (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")]),
      Function (mkCId "a") (Fun (mkCId "A") []),
      Function (mkCId "b") (Fun (mkCId "B") []),
      Function (mkCId "c") (Fun (mkCId "C") [])
     ]
--           generate grammar 2
-- ==> [({?A}, [([], {?A})]),
--      ({{a:A}}, []),
--      ({{f:A ?A ?B}}, [([0], {?A}), ([1], {?B})]),
--      ({{f:A {a:A} ?B}}, [([1], {?B})]),
--      ({{f:A {f:A ?A ?B} ?B}}, [([0,0], {?A}), ([0,1], {?B}), ([1], {?B})]),
--      ({{f:A ?A {b:B}}}, [([0], {?A})]),
--      ({{f:A {a:A} {b:B}}}, []),
--      ({{f:A {f:A ?A ?B} {b:B}}}, [([0,0], {?A}), ([0,1], {?B})]),
--      ({{f:A ?A {b:B}}}, [([0], {?A})]),
--      ({{f:A {a:A} {g:B ?B ?C}}}, [([1,0], {{b:B}}), ([1,1], {{c:C}})]),
--      ...
--      ]

-- match ({{f:A ?A ?B}}, [([0], {{a:A}}), ([1], {{g:B {b:B} {c:C}}})])
--       ({{f:A {f:A ?A ?B} {b:B}}}, [([0,0], {?A}), ([0,1], {?B})])
-- ==> (1+3, {{f:A {f:A {a:A} {g:B {b:B} {c:C}}} {b:B}}})
-- -- (the cost 1 is because the splitted_tree has 1 node, and 3 is because the generated_tree has 3 nodes)
test_hu_match1 =
    do
      let tree1 = (MetaTTree (read "{f:A {?A} {?B}}") [([0], read "{a:A}"), ([1], read "{g:B {b:B} {c:C}}")])
      let tree2 = (MetaTTree (read "{f:A {f:A ?A ?B} {b:B}}") [([0,0], read "{?A}"), ([0,1], read "{?B}")])
      let result = (1+3, read "{f:(A -> B -> A) {f:(A -> B -> A) {a:A} {g:(B -> C -> B) {b:B} {c:C}}} {b:B}}") :: (Cost,TTree)
      runTestTT ((head $ match tree1 tree2) ~?= result)
-- match ({{f:A ?A ?B}}, [([0], {{a:A}}), ([1], {{g:B {b:B} {c:C}}})])
--       ({{f:A ?A {b:B}}}, [([0], {?A})])
-- ==> [(1+2+3, {{f:A {a:A} {b:B}}})]
-- -- (the cost 1 is because the splitted_tree has 1 node, and 2 is because the generated_tree has 2 nodes; the cost 3 is because the B tree was removed, and it has 3 nodes)
test_hu_match2 =
    do
      let tree1 = (MetaTTree (read "{f:A ?A ?B}") [([0], read "{a:A}"), ([1], read "{g:B {b:B} {c:C}}")])
      let tree2 = (MetaTTree (read "{f:A ?A {b:B}}") [([0], read "{?A}")])
      let result = (1+2+3, read "{f:A {a:A} {b:B}}") :: (Cost,TTree)
      runTestTT ((head $ match tree1 tree2) ~?= result)
hunit_tests =
  do
    test_hu_read1
    test_hu_read2
    test_hu_read3
    test_hu_prune
    test_hu_match1
    test_hu_match2
    
-- Quickcheck tests
instance Arbitrary TTree where
  arbitrary =
    do
      let generated = Tree.generate grammar (mkCId "A") 5
      elements (map metaTree generated)

prop_metaTest :: TTree -> Bool
prop_metaTest tree =
  (getMetaLeaves tree) == map snd (getMetaPaths tree)
test_qc_meta1 =
  quickCheckWith stdArgs { maxSuccess = 500 } prop_metaTest

-- prop_generateTest :: Int -> Bool
-- prop_generateTest depth =
--   (Tree.generate g1 (mkCId "A") depth) ==  (generate' g1 (mkCId "A") depth)

quickcheck_tests =
  do
    putStrLn "Quickcheck MetaEquality"
    test_qc_meta1
-- Main
main =
  do
    putStrLn "HUnite tests:"
    hunit_tests
    --putStrLn "Quickcheck tests:"
    --quickcheck_tests

