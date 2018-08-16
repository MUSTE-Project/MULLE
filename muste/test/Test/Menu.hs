{-# Language UnicodeSyntax, NamedWildCards, TemplateHaskell #-}
module Test.Menu (tests) where

import Data.Semigroup
import Data.Maybe
import Test.Tasty
import Test.Tasty.HUnit
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Containers as Mono
import Data.ByteString (ByteString)
import qualified Data.ByteString.Lazy as LB

import Muste.Common
import Muste (Grammar, Context, TTree, Menu, Linearization)
import qualified Muste as Muste
import qualified Muste.Grammar.Internal as Grammar
import qualified Muste.Menu.Internal as Menu
import qualified Muste.Linearization.Internal as Linearization
import qualified Muste.Grammar.Embed as Embed
import qualified Muste.Selection as Selection
import Muste.Grammar.TH (tree)

import Muste.Common

grammar :: Grammar
grammar = Grammar.parseGrammar $ LB.fromStrict $ snd grammar'
  where
  grammar' ∷ (String, ByteString)
  grammar' = $(Embed.grammar "novo_modo/Prima")

ctxts ∷ Map String Context
ctxts = Linearization.readLangs grammar

ambiguities ∷ Assertion
ambiguities = treeDefiniteL @?= treeIndefiniteL

menu ∷ Menu
menu = getMenu treeDefinite

treeDefinite ∷ TTree
treeDefinite = $(tree "novo_modo/Prima"
  $  "useS (useCl (simpleCl "
  <>   "(useCNdefsg (useN hostis_N))"
  <>   "(transV vincere_V2 (usePN Africa_PN))))")

treeDefiniteL ∷ Linearization
treeDefiniteL = mkLin treeDefinite

treeIndefinite ∷ TTree
treeIndefinite = $(tree "novo_modo/Prima"
  $ "useS (useCl (simpleCl (useCNindefsg (useN hostis_N)) "
  <>            "(transV vincere_V2 (usePN Africa_PN))))")

treeIndefiniteL ∷ Linearization
treeIndefiniteL = mkLin treeIndefinite

getMenu ∷ TTree → Menu
getMenu = Muste.getCleanMenu latinCtxt

latinCtxt ∷ Context
latinCtxt = fromMaybe (error "Can't find Latin context")
  $ Map.lookup "PrimaLat" ctxts

mkLin ∷ TTree → Linearization
mkLin = Linearization.mkLin latinCtxt treeDefinite treeIndefinite

tests ∷ TestTree
tests =
  testGroup "Prune"
    [ "The (in-)definite form in latin is ambiguous" |> ambiguities
    ]
  where
  (|>) = testCase
