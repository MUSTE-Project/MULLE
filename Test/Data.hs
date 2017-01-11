module Test.Data where
import PGF
import PGF.Internal
import Muste.Grammar.Internal
import Muste.Tree
import Data.Set

grammar = Grammar (mkCId "A")
     [
      Function (mkCId "f") (Fun (mkCId "A") [mkCId "A",mkCId "A"]),
      Function (mkCId "a") (Fun (mkCId "A") [])
     ]
  emptyPGF

tree1 = TMeta (mkCId "A")

tree2 = TNode (mkCId "a") (Fun (mkCId "A") []) []
