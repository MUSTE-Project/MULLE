import Test.QuickCheck
import PGF
import Tree
import Grammar
import Data.List
import Test.HUnit.Text
import Test.HUnit.Base
import System.Random

randomize :: StdGen -> [a] -> [a]
randomize _ [] = []
randomize gen list =
  let
    (rnd, ngen) = randomR (0,length list - 1) gen
    (part1,_:part2) = splitAt rnd list
  in
    (list !! rnd) : (randomize ngen (part1 ++ part2))
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

-- read equality Test 4
{-
  reads the tree as a string and compares with the data structure
  also fixes the types
-}          
ts6 = "{t2:F {?A} {g:G {?B} {h:H {?C} {i:I {?D} {?E}}}}}"
test_hu_read4 =
  do
    putStrLn "Check read equality Test 4"
    runTestTT (t2 ~?= (read ts6 :: TTree))

-- read equality Test 5
{-
  reads the tree as a string and compares with the data structure
  also fixes the types
-}          
ts7 = "{t4:A {?A} {?A}}"
test_hu_read5 =
  do
    putStrLn "Check read equality Test 5"
    runTestTT (t4 ~?= (read ts7 :: TTree))

-- ord Test 1
{-
  checks trees t1 <= t2
-}          
test_hu_ord1 =
  do
    putStrLn "Check tree order Test 1"
    runTestTT (t1 <= t2 ~?= True)

-- ord Test 2
{-
  checks trees t1 < t2
-}          
test_hu_ord2 =
  do
    putStrLn "Check tree order Test 2"
    runTestTT (t1 < t2 ~?= True)

-- ord Test 3
{-
  checks trees t1 == t2
-}          
test_hu_ord3 =
  do
    putStrLn "Check tree order Test 3"
    runTestTT (t1 == t2 ~?= False)

-- ord Test 4
{-
  checks trees t1 > t2
-}          
test_hu_ord4 =
  do
    putStrLn "Check tree order Test 4"
    runTestTT (t1 > t2 ~?= False)

-- ord Test 5
{-
  checks trees t1 == t1
-}          
test_hu_ord5 =
  do
    putStrLn "Check tree order Test 5"
    runTestTT (t1 == t1 ~?= True)

-- ord Test 6
{-
  checks trees t1 <= t1
-}          
test_hu_ord6 =
  do
    putStrLn "Check tree order Test 6"
    runTestTT (t1 <= t1 ~?= True)

    
t3 = let (MetaTTree (TNode _ typ trees) subTrees) = replaceNodeByMeta (replaceNodeByMeta (makeMeta t1) [1,0]) [1,1] in (MetaTTree (TNode (mkCId "t3") typ trees) subTrees)

test_hu_sort =
  do
    let list = [t1,t2,t4]
    gen <- getStdGen
    putStrLn "Sort tree order Test"
--    runTestTT ((sort $ randomize list gen) ~?= [t4,t1,t2])
    runTestTT ((sort $ randomize gen list) ~?= (sort $ sort $ randomize gen $ sort $ randomize gen list))
    
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
  do
    putStrLn "Check prune Test"
    let tree = (read "{f:(A -> B -> A) {a:A} {g:B {b:B} {c:C}}}") :: TTree
    let result = [(MetaTTree (read "{?A}") [([], read "{f:(A -> B -> A) {a:A} {g:B {b:B} {c:C}}}")]),
                  (MetaTTree (read "{f:(A -> B -> A) {?A} {?B}}") [([0], read "{a:A}"), ([1], read "{g:(B -> C -> B) {b:B} {c:C}}")]),
                  (MetaTTree (read "{f:(A -> B -> A) {a:A} {?B}}") [([1], read "{g:(B -> C -> B) {b:B} {c:C}}")]),
                  (MetaTTree (read "{f:(A -> B -> A) {?A} {g:(B -> C -> B) {?B} {?C}}}") [([0], read "{a:A}"), ([1,0], read "{b:B}"), ([1,1], read "{c:C}")]),
                  (MetaTTree (read "{f:(A -> B -> A) {?A} {g:(B -> C -> B) {b:B} {?C}}}") [([0], read "{a:A}"), ([1,1], read "{c:C}")]),
                  (MetaTTree (read "{f:(A -> B -> A) {?A} {g:(B -> C -> B) {?B} {c:C}}}") [([0], read "{a:A}"), ([1,0], read "{b:B}")]),
                  (MetaTTree (read "{f:(A -> B -> A) {?A} {g:(B -> C -> B) {b:B} {c:C}}}") [([0], read "{a:A}"), ([1,1], read "{c:C}")]),
                  (MetaTTree (read "{f:(A -> B -> A) {a:A} {g:(B -> C -> B) {?B} {?C}}}") [([1,0], read "{b:B}"), ([1,1], read "{c:C}")]),
                  (MetaTTree (read "{f:(A -> B -> A) {a:A} {g:(B -> C -> B) {b:B} {?C}}}") [([1,1], read "{c:C}")]),
                  (MetaTTree (read "{f:(A -> B -> A) {a:A} {g:(B -> C -> B) {?B} {c:C}}}") [([1,0], read "{b:B}")]),
                  (MetaTTree (read "{f:(A -> B -> A) {a:A} {g:(B -> C -> B) {b:B} {c:C}}}") [])
                 ]
    --putStrLn $ show (prune tree 2)
    runTestTT ((sort $ prune tree 2) ~?= (sort result))
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
test_hu_generate =
  do
    putStrLn "Check generate Test 1"
    let result= [(MetaTTree (read "{?A}") [([], read "{?A}")]),
                 (MetaTTree (read "{a:A}") []),
                 (MetaTTree (read "{f:A {?A} {?B}}") [([0], read "{?A}"), ([1], read "{?B}")]),
                 (MetaTTree (read "{f:A {a:A} {?B}}") [([1], read "{?B}")]),
                 (MetaTTree (read "{f:A {f:A {?A} {?B}} {?B}}") [([0,0], read "{?A}"), ([0,1], read "{?B}"), ([1], read "{?B}")]),
                 (MetaTTree (read "{f:A {?A} {b:B}") [([0], read "{?A}")]),
                 (MetaTTree (read "{f:A {a:A} {b:B}}") []),
                 (MetaTTree (read "{f:A {f:A {?A} {?B}} {b:B}}") [([0,0], read "{?A}"), ([0,1], read "{?B}")]),
                 (MetaTTree (read "{f:A {?A} {b:B}}") [([0], read "{?A}")]),
                 (MetaTTree (read "{f:A {a:A} {g:B {?B} {?C}}}") [([1,0], read "{b:B}"), ([1,1], read "{c:C}")])
                ]:: [MetaTTree]
    runTestTT ((Tree.generate grammar (mkCId "A") 2) ~?= result)
    
-- match ({{f:A ?A ?B}}, [([0], {{a:A}}), ([1], {{g:B {b:B} {c:C}}})])
--       ({{f:A {f:A ?A ?B} {b:B}}}, [([0,0], {?A}), ([0,1], {?B})])
-- ==> (1+3, {{f:A {f:A {a:A} {g:B {b:B} {c:C}}} {b:B}}})
-- -- (the cost 1 is because the splitted_tree has 1 node, and 3 is because the generated_tree has 3 nodes)
test_hu_match1 =
    do
      putStrLn "Check match Test 1"
      let tree1 = (MetaTTree (read "{f:(A -> B -> A) {?A} {?B}}") [([0], read "{a:A}"), ([1], read "{g:(B -> C -> B) {b:B} {c:C}}")])
      let tree2 = (MetaTTree (read "{f:(A -> B -> A) {f:(A -> B -> A) {?A} {?B}} {b:B}}") [([0,0], read "{?A}"), ([0,1], read "{?B}")])
      let result = (1+3, read "{f:(A -> B -> A) {f:(A -> B -> A) {a:A} {g:(B -> C -> B) {b:B} {c:C}}} {b:B}}") :: (Cost,TTree)
      runTestTT ((head $ match tree1 tree2) ~?= result)
-- match ({{f:A ?A ?B}}, [([0], {{a:A}}), ([1], {{g:B {b:B} {c:C}}})])
--       ({{f:A ?A {b:B}}}, [([0], {?A})])
-- ==> [(1+2+3, {{f:A {a:A} {b:B}}})]
-- -- (the cost 1 is because the splitted_tree has 1 node, and 2 is because the generated_tree has 2 nodes; the cost 3 is because the B tree was removed, and it has 3 nodes)
test_hu_match2 =
    do
      putStrLn "Check match Test 2"
      let tree1 = (MetaTTree (read "{f:A {?A} {?B}}") [([0], read "{a:A}"), ([1], read "{g:B {b:B} {c:C}}")])
      let tree2 = (MetaTTree (read "{f:A {?A} {b:B}}") [([0], read "{?A}")])
      let result = (1+2+3, read "{f:A {a:A} {b:B}}") :: (Cost,TTree)

      runTestTT ((head $ match tree1 tree2) ~?= result)
hunit_tests =
  do
    test_hu_read1
    test_hu_read2
    test_hu_read3
    test_hu_read4
    test_hu_read5
    test_hu_prune
    test_hu_generate
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

