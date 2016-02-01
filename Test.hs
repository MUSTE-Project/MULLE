import Test.QuickCheck
import PGF
import Tree
import Grammar
import Data.List
-- import Test.HUnit

instance Arbitrary TTree where
  arbitrary =
    do
      let generated = Tree.generate g1 (mkCId "A") 5
      elements (map metaTree generated)

prop_metaTest :: TTree -> Bool
prop_metaTest tree =
  (getMetaLeaves tree) == map snd (getMetaPaths tree)

prop_generateTest :: Int -> Bool
prop_generateTest depth =
  (Tree.generate g1 (mkCId "A") depth) ==  (generate' g1 (mkCId "A") depth)
main =
  do
    quickCheckWith stdArgs { maxSuccess = 5 } prop_generateTest

t = (TNode (mkCId "t") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TNode (mkCId "a") (Fun (mkCId "A") []) []),(TNode (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")]) [(TNode (mkCId "b") (Fun (mkCId "B") []) []),(TNode (mkCId "c") (Fun (mkCId "C") []) [])])])

t2 = (TNode (mkCId "t2") (Fun (mkCId "F") [(mkCId "A"), (mkCId "G")]) [(TMeta (mkCId "A")), (TNode (mkCId "g") (Fun (mkCId "G") [(mkCId "B"), (mkCId "H")]) [(TMeta (mkCId "B")), (TNode (mkCId "h") (Fun (mkCId "H") [(mkCId "C"), (mkCId "I")]) [(TMeta (mkCId "C")), (TNode (mkCId "i") (Fun (mkCId "I") [(mkCId "D"),(mkCId "E")]) [(TMeta (mkCId "D")), (TMeta (mkCId "E"))])])])])

t3 = let (MetaTTree (TNode _ typ trees) subTrees) = replaceNodeByMeta (replaceNodeByMeta (makeMeta t) [1,0]) [1,1] in (MetaTTree (TNode (mkCId "t3") typ trees) subTrees)

t4 = (TNode (mkCId "t4") (Fun (mkCId "A") [(mkCId "A"),(mkCId "A")]) [(TMeta (mkCId "A")), (TMeta (mkCId "A"))])

g1 = Grammar (mkCId "A")
     [
      Function (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]),
      Function (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")]),
      Function (mkCId "a") (Fun (mkCId "A") []),
      Function (mkCId "b") (Fun (mkCId "B") []),
      Function (mkCId "c") (Fun (mkCId "C") [])
     ]
g2 = Grammar (mkCId "A")
     [
      Function (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "A")]),
      Function (mkCId "a") (Fun (mkCId "A") []) -- ,
--      Function (mkCId "aa") (Fun (mkCId "A") [(mkCId "A")])
     ]

r1 = Function (mkCId "b") (Fun (mkCId "B") [])

r2 = Function (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")])

r3 = Function (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "A")])

--main =
--    generate g1 (mkCId "A") 2


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
