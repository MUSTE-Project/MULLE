{-# Language UnicodeSyntax, NamedWildCards, TemplateHaskell #-}
module Test.Linearization (tests) where

import Data.Semigroup
import Data.Maybe
import Test.Tasty
import Test.Tasty.HUnit
import Data.Map (Map)
import qualified Data.Map as Map

import Muste (Grammar, Context, TTree, Linearization)
import qualified Muste.Linearization.Internal as Linearization
import Muste.Grammar.TH (tree)

import qualified Test.Common as Test

grammar :: Grammar
grammar = Test.grammar

ctxts ∷ Map String Context
ctxts = Linearization.readLangs grammar

ambiguities ∷ Assertion
ambiguities = treeDefiniteL @?= treeIndefiniteL

treeDefinite ∷ TTree
treeDefinite = $(tree "novo_modo/Exemplum"
  $  "useS (useCl (simpleCl "
  <>   "(useCNdefsg (useN hostis_N))"
  <>   "(transV vincere_V2 (usePN Africa_PN))))")

treeDefiniteL ∷ Linearization
treeDefiniteL = mkLin treeDefinite

treeIndefinite ∷ TTree
treeIndefinite = $(tree "novo_modo/Exemplum"
  $ "useS (useCl (simpleCl (useCNindefsg (useN hostis_N)) "
  <>            "(transV vincere_V2 (usePN Africa_PN))))")

treeIndefiniteL ∷ Linearization
treeIndefiniteL = mkLin treeIndefinite

latCtxt ∷ Context
latCtxt = fromMaybe (error "Can't find Latin context")
  $ Map.lookup "ExemplumLat" ctxts

mkLin ∷ TTree → Linearization
mkLin = Linearization.mkLin theCtxt treeDefinite treeIndefinite

theCtxt ∷ Context
theCtxt = latCtxt

tests ∷ TestTree
tests =
  testGroup "Linearization"
    [ "The (in-)definite form in latin is ambiguous" |> ambiguities
    ]
  where
  (|>) = testCase
