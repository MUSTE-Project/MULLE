{- | Implements several tests to control the validy of the program
-}
module Test.Tree where
import Test.QuickCheck
import PGF
import PGF.Internal
import Muste.Tree.Internal
import Muste.Grammar
import Data.List
import Test.HUnit.Text
import Test.HUnit.Base
import System.Random
import Data.Set (Set,fromList,toList,empty)
import Test.Data

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

{- | The test 'test_hu_read1' reads the tree as a string and compares with the data structure, a simple tree
-}
test_hu_read1 =
  do
    putStrLn "Check read equality Test 1"
    runTestTT (t1 ~?= (read ts1 :: TTree))

-- read equality Test 2
{- | The test 'test_hu_read2' reads the tree as a string and compares with the data structure, a quite deep tree
-}
test_hu_read2 =
  do
    putStrLn "Check read equality Test 2"
    runTestTT (t2 ~?= (read ts2 :: TTree))

-- read equality Test 3
{- | The test 'test_hu_read3' reads the tree as a string and compares with the data structure, all subtrees are metas
-}
test_hu_read3 =
  do
    putStrLn "Check read equality Test 3"
    runTestTT (t4 ~?= (read ts4 :: TTree))

-- read equality Test 4
{-
  reads the tree as a string and compares with the data structure
  also fixes the types
-}

test_hu_read4 =
  do
    putStrLn "Check read equality Test 4"
    runTestTT (t2 ~?= (read ts6 :: TTree))
    
-- read equality Test 5
{-
  reads the tree as a string and compares with the data structure
  also fixes the types
-}          
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
    let result = fromList $ [(MetaTTree (read "{?A}") $ fromList [([], read "{f:(A -> B -> A) {a:A} {g:B {b:B} {c:C}}}")]),
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
        sorted1 = prune tree 2
        sorted2 = result
    --putStrLn $ show (prune tree 2)
    runTestTT ((sorted1) ~?= (sorted2)) 
    
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
  emptyPGF
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
    let result= fromList [(MetaTTree (read "{?A}") $ fromList [([], read "{?A}")]),
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
    runTestTT ((Muste.Tree.Internal.generate grammar (mkCId "A") 2) ~?= result)
    
-- match ({{f:A ?A ?B}}, [([0], {{a:A}}), ([1], {{g:B {b:B} {c:C}}})])
--       ({{f:A {f:A ?A ?B} {b:B}}}, [([0,0], {?A}), ([0,1], {?B})])
-- ==> (1+3, {{f:A {f:A {a:A} {g:B {b:B} {c:C}}} {b:B}}})
-- -- (the cost 1 is because the splitted_tree has 1 node, and 3 is because the generated_tree has 3 nodes)
test_hu_match1 =
    do
      putStrLn "Check match Test 1"
      let tree1 = (MetaTTree (read "{f:(A -> B -> A) {?A} {?B}}") $ fromList [([0], read "{a:A}"), ([1], read "{g:(B -> C -> B) {b:B} {c:C}}")])
      let tree2 = (MetaTTree (read "{f:(A -> B -> A) {f:(A -> B -> A) {?A} {?B}} {b:B}}") $ fromList [([0,0], read "{?A}"), ([0,1], read "{?B}")])
      let result = (1+3, read "{f:(A -> B -> A) {f:(A -> B -> A) {a:A} {g:(B -> C -> B) {b:B} {c:C}}} {b:B}}") :: (Cost,TTree)
      runTestTT ((head $ match tree1 tree2) ~?= result)
-- match ({{f:A ?A ?B}}, [([0], {{a:A}}), ([1], {{g:B {b:B} {c:C}}})])
--       ({{f:A ?A {b:B}}}, [([0], {?A})])
-- ==> [(1+2+3, {{f:A {a:A} {b:B}}})]
-- -- (the cost 1 is because the splitted_tree has 1 node, and 2 is because the generated_tree has 2 nodes; the cost 3 is because the B tree was removed, and it has 3 nodes)
test_hu_match2 =
    do
      putStrLn "Check match Test 2"
      let tree1 = (MetaTTree (read "{f:A {?A} {?B}}") $ fromList [([0], read "{a:A}"), ([1], read "{g:B {b:B} {c:C}}")])
      let tree2 = (MetaTTree (read "{f:A {?A} {b:B}}") $ fromList [([0], read "{?A}")])
      let result = (1+2+3, read "{f:A {a:A} {b:B}}") :: (Cost,TTree)

      runTestTT ((head $ match tree1 tree2) ~?= result)

test_hu_ttreetogfabstree1 =
  do
    putStrLn "Check ttreeToGFAbsTree Test 1"
    let abstree = (EFun (mkCId "foo"))
    let ttree = read "{foo:()}" :: TTree
    runTestTT (ttreeToGFAbsTree ttree ~?= abstree)

test_hu_typecheck = 
  do
    putStrLn "Check typecheck Test 1"
    let ttree = read "{foo:(Bar -> Baz) {bar:Bar2}}" :: TTree
    runTestTT (typecheck ttree ~?= False)
    putStrLn "Check typecheck Test 2"
    let ttree = read "{baz:(Foo -> Bar -> Baz) {foo:Foo}}" :: TTree
    runTestTT (typecheck ttree ~?= False)
    putStrLn "Check typecheck Test 3"
    let ttree = read "{foo:(Bar)}" :: TTree
    runTestTT (typecheck ttree ~?= True)

test_hu_getchildcats =
  do
    putStrLn "Check getchildcat Test 1"
    let ttree = read "{foo:(Bar -> Baz) {bar:Bar2}}" :: TTree
    runTestTT (getChildCats ttree ~?= [(mkCId "Bar2")])
    putStrLn "Check getchildcat Test 2"
    let ttree = read "{baz:(Foo -> Bar -> Baz) {foo:Foo} {bar:(Bla -> Blubb -> Bar) {bla:Bla} {blubb:Blubb}}}" :: TTree
    runTestTT (getChildCats ttree ~?= [(mkCId "Foo"),(mkCId "Bar")])
      
test_hu_gfabstreetottree =
  do
    pgf <- readPGF "gf/ABCAbs.pgf"
    runTestTT (1 ~?= 0)
hunit_tests =
  do
    test_hu_read1
    test_hu_read2
    test_hu_read3
    test_hu_read4
    test_hu_read5
    test_hu_ord1
    test_hu_ord2
    test_hu_ord3
    test_hu_ord4
    test_hu_ord5
    test_hu_ord6
    test_hu_sort
    test_hu_prune
    test_hu_generate
    test_hu_match1
    test_hu_match2
    test_hu_ttreetogfabstree1
--    test_hu_ttreetogfabstree2
    test_hu_typecheck
    test_hu_getchildcats
    test_hu_gfabstreetottree
-- Quickcheck tests
instance Arbitrary TTree where
  arbitrary =
    do
      let generated = toList $ Muste.Tree.Internal.generate grammar (mkCId "A") 5
      elements (map metaTree generated)

-- prop_metaTest :: TTree -> Bool
-- prop_metaTest tree =
--   (getMetaLeaves tree) == map snd (getMetaPaths tree)
-- test_qc_meta1 =
--   quickCheckWith stdArgs { maxSuccess = 500 } prop_metaTest

-- prop_generateTest :: Int -> Bool
-- prop_generateTest depth =
--   (Tree.generate g1 (mkCId "A") depth) ==  (generate' g1 (mkCId "A") depth)

-- quickcheck_tests =
--   do
--     putStrLn "Quickcheck MetaEquality"
--     test_qc_meta1
-- Main
main =
  do
    putStrLn "HUnite tests:"
    hunit_tests
    --putStrLn "Quickcheck tests:"
    --quickcheck_tests

