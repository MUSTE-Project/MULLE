module Test.Data where
import PGF
import PGF.Internal
import Muste.Grammar.Internal
import Muste.Tree
import Data.Set

t1 = (TNode (mkCId "t1") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) [(TNode (mkCId "a") (Fun (mkCId "A") []) []),(TNode (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")]) [(TNode (mkCId "b") (Fun (mkCId "B") []) []),(TNode (mkCId "c") (Fun (mkCId "C") []) [])])])

t2 = (TNode (mkCId "t2") (Fun (mkCId "F") [(mkCId "A"), (mkCId "G")]) [(TMeta (mkCId "A")), (TNode (mkCId "g") (Fun (mkCId "G") [(mkCId "B"), (mkCId "H")]) [(TMeta (mkCId "B")), (TNode (mkCId "h") (Fun (mkCId "H") [(mkCId "C"), (mkCId "I")]) [(TMeta (mkCId "C")), (TNode (mkCId "i") (Fun (mkCId "I") [(mkCId "D"),(mkCId "E")]) [(TMeta (mkCId "D")), (TMeta (mkCId "E"))])])])])

t4 = (TNode (mkCId "t4") (Fun (mkCId "A") [(mkCId "A"),(mkCId "A")]) [(TMeta (mkCId "A")), (TMeta (mkCId "A"))])

ts1 = "{t1:(A -> B -> A) {a:A} {g:(B -> C -> B) {b:B} {c:C}}}"
ts2 = "{t2:(A -> G -> F) {?A} {g:(B -> H -> G) {?B} {h:(C -> I -> H) {?C} {i:(D -> E -> I) {?D} {?E}}}}}"
ts4 = "{t4:(A -> A -> A) {?A} {?A}}"
ts6 = "{t2:F {?A} {g:G {?B} {h:H {?C} {i:I {?D} {?E}}}}}"
ts7 = "{t4:A {?A} {?A}}"

grammar = Grammar (mkCId "A")
     [
      Function (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "A")]),
      Function (mkCId "a") (Fun (mkCId "A") []) -- ,
--      Function (mkCId "aa") (Fun (mkCId "A") [(mkCId "A")])
     ]
  emptyPGF

r1 = Function (mkCId "b") (Fun (mkCId "B") [])

r2 = Function (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")])

r3 = Function (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "A")])

mt11 =
  -- (MetaTTree 
  --  (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"), (mkCId "B")])
  --   [
  --      (TMeta (mkCId "A")),
  --      (TMeta (mkCId "B"))
  --   ]
  --  )
  --  $ fromList [([0], (TNode (mkCId "a") (Fun (mkCId "A") []) [])),
  --              ([1], (TNode (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")])
  --                     [
  --                       (TNode (mkCId "b") (Fun (mkCId "B") []) []),
  --                       (TNode (mkCId "c") (Fun (mkCId "C") []) [])
  --                     ]
  --                    )
  --              )
  --             ]
  -- )
  (MetaTTree 
   (read "{f:(A -> B -> A) {?A} {?B}}")
   $ fromList [([0], (read "{a(A)}")),
               ([1], (read "{g:(B -> C -> B) {b:(B)} {c:(C)}}"))
              ]
  )
mt12 =
  -- (MetaTTree
  --  (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
  --   [
  --     (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
  --      [
  --        (TMeta (mkCId "A")),
  --        (TMeta (mkCId "B"))
  --      ]
  --     ),
  --     (TNode (mkCId "b") (Fun (mkCId "B") []) [])
  --   ]
  --  )
  --  $ fromList [([0,0], (TMeta (mkCId "A"))),
  --   ([0,1], (TMeta (mkCId "B")))
  --  ]
  -- )
  (MetaTTree
   (read "{f:(A -> B -> A) {f:(A -> B -> A) {?A} {?B}} {b:(B)}}")
   $ fromList [([0,0], (read "{?A}")),
    ([0,1], (read "{?B}"))
   ]
  )
rt1 =
  -- (4,
  --  (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
  --   [
  --     (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
  --      [
  --        (TNode (mkCId "a") (Fun (mkCId "A") []) []),
  --        (TNode (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")])
  --         [
  --           (TNode (mkCId "b") (Fun (mkCId "B") []) []),
  --           (TNode (mkCId "c") (Fun (mkCId "C") []) [])
  --         ]
  --        )
  --      ]),
  --     (TNode (mkCId "b") (Fun (mkCId "B") []) [])
  --   ]
  --  )
  -- )
  (4, (read "{f:(A -> B -> A) {f:(A -> B -> A) {a:(A)} {g:(B -> C -> B) {b:(B)} {c:C}}}}") :: TTree)
-- (the cost 1 is because the splitted_tree has 1 node, and 3 is because the generated_tree has 3 nodes)
-- Not working yet
mt21 =
  -- (MetaTTree
  --  (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"), (mkCId "B")])
  --   [
  --     (TMeta (mkCId "A")),
  --     (TMeta (mkCId "B"))
  --   ]
  --  )
  --  $ fromList [
  --    ([0], (TNode (mkCId "a") (Fun (mkCId "A") []) [])),
  --    ([1], (TNode (mkCId "g") (Fun (mkCId "B") [(mkCId "B"), (mkCId "C")])
  --           [
  --             (TNode (mkCId "b") (Fun (mkCId "B") []) []),
  --             (TNode (mkCId "c") (Fun (mkCId "C") []) [])
  --           ]
  --          )
  --    )
  --  ]
  -- )
  (MetaTTree
   (read "{f:(A -> B -> A) {?A} {?B}}")
   $ fromList [
     ([0], (read "{a:(A)}")),
     ([1], (read "{g:(B -> C -> B) {b:B} {c:C}}"))
   ]
  )
mt22 =
  -- (MetaTTree
  --  (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"), (mkCId "B")])
  --   [
  --     (TMeta (mkCId "A")),
  --     (TNode (mkCId "b") (Fun (mkCId "B") []) [])
  --   ]
  --  )
  --  $ fromList [
  --    ([0], (TMeta (mkCId "A")))
  --  ]
  -- )
  (MetaTTree
   (read "{f:(A -> B -> A) {?A} {b:B}}")
   $ fromList [
     ([0], (read "{?A}"))
   ]
  )
rt2 =
  -- ( 6,
  --  (TNode (mkCId "f") (Fun (mkCId "A") [(mkCId "A"), (mkCId "B")])
  --   [
  --     (TNode (mkCId "a") (Fun (mkCId "A") []) []),
  --     (TNode (mkCId "b") (Fun (mkCId "B") []) [])
  --   ]
  --  )
  -- )
  (6,
   (read "{f:(A -> B -> A) {a:(A)} {b:B}}") :: TTree
  )
