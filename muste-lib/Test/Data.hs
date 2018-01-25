module Test.Data where
import PGF
import PGF.Internal
import Muste.Grammar.Internal
import Muste.Tree
import Data.Set

grammar = Grammar "A"
  [
    Function "f" (Fun "A" ["A","A"])
  ]
  [
      Function "a" (Fun "A" [])
  ]
  emptyPGF

tree1 = TMeta "A"

tree2 = TNode "a" (Fun "A" []) []
