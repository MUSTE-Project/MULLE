{-# Language UnicodeSyntax, NamedWildCards, TemplateHaskell #-}
-- TODO Still need to add test-case that uses a menu.
{-# OPTIONS_GHC -Wno-all #-}
module Test.Menu (tests) where

import Data.Semigroup
import Data.Maybe
import Test.Tasty
import Test.Tasty.HUnit
import Data.Map (Map)
import qualified Data.Map as Map
import Data.ByteString (ByteString)
import qualified Data.ByteString.Lazy as LB

import Muste (Grammar, Context, TTree, Menu, Linearization)
import qualified Muste
import qualified Muste.Grammar.Internal as Grammar
import qualified Muste.Linearization.Internal as Linearization
import qualified Muste.Grammar.Embed as Embed
import Muste.Grammar.TH (tree)

import qualified Test.Common as Test

grammar :: Grammar
grammar = Test.grammar

ctxts ∷ Map String Context
ctxts = Linearization.readLangs grammar

ambiguities ∷ Assertion
ambiguities = treeDefiniteL @?= treeIndefiniteL

menu ∷ Menu
menu = getMenu treeDefinite

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

getMenu ∷ TTree → Menu
getMenu = Muste.getCleanMenu theCtxt

getMenu' ∷ Linearization → Menu
getMenu' = Muste.getMenu theCtxt

latCtxt ∷ Context
latCtxt = fromMaybe (error "Can't find Latin context")
  $ Map.lookup "ExemplumLat" ctxts

sweCtxt ∷ Context
sweCtxt = fromMaybe (error "Can't find Swedish context")
  $ Map.lookup "ExemplumSwe" ctxts

mkLin ∷ TTree → Linearization
mkLin = Linearization.mkLin theCtxt treeDefinite treeIndefinite

theCtxt = sweCtxt
tests ∷ TestTree
tests =
  testGroup "Menu"
    [ "The (in-)definite form in latin is ambiguous" |> ambiguities
    ]
  where
  (|>) = testCase
