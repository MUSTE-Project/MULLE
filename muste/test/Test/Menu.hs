{-# Language UnicodeSyntax, NamedWildCards, TemplateHaskell #-}
-- TODO Still need to add test-case that uses a menu.
{-# OPTIONS_GHC -Wall #-}
module Test.Menu (tests) where

import Data.Maybe
import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Category ((>>>))
import Control.Monad.Fail (MonadFail)
import Text.Printf
import Data.Containers (IsMap)
import qualified Data.Containers as Mono
import Data.Text.Prettyprint.Doc (pretty)

import Muste (Grammar, TTree, Menu, Linearization, Context)
import qualified Muste
import qualified Muste.Common as Common
import qualified Muste.Grammar.Internal as Grammar
import qualified Muste.Linearization.Internal as Linearization
import qualified Muste.Menu.Internal as Menu
import Muste.Selection (Selection)
import qualified Muste.Selection as Selection

import qualified Test.Common as Test

grammar :: Grammar
grammar = Test.grammar

getMenu ∷ TTree → TTree → TTree → Menu
getMenu src trg = mkLin src trg >>> Muste.getMenu theCtxt

mkLin ∷ TTree → TTree → TTree → Linearization
mkLin src trg = Linearization.mkLin theCtxt src trg

theCtxt ∷ Context
theCtxt = fromMaybe (error "Can't find Swedish context")
  $ Map.lookup "ExemplumSwe" $ Linearization.readLangs grammar

tests ∷ TestTree
tests = testGroup "Menu" $ mkTests
  [ ("name", "source tree", [0], "target tree")
  ]

mkTests ∷ [(String, String, [Int], String)] → [TestTree]
mkTests = map go
  where
  go ∷ (String, String, [Int], String) → TestTree
  go (nm, src, n, trg) = testCase nm
    $ assertThere (parseTree src) (Selection.fromList n) (parseTree trg)

-- | @'assertThere' src n trg@ asserts that @trg@ exists in the menu
-- you get from @src@.
assertThere ∷ TTree → Selection → TTree → Assertion
assertThere src n trg = do
  cts ← lookupMenu err (getMenu src trg src)
  Mono.member (mkLin src trg trg) cts @?= True
  where
  lookupMenu ∷ ∀ m . MonadFail m ⇒ String → Menu → m (Set Linearization)
  -- lookup mn = undefined
  lookupMenu s mn
    = Set.fromList . fmap Menu.lin
    <$> lookupFail s n mn
  err ∷ String
  err = printf "Test.Menu.assertThere: Selection not in tree: (%s)"
    $ show $ pretty n

lookupFail
  ∷ MonadFail m
  ⇒ IsMap map
  ⇒ String
  → Mono.ContainerKey map
  → map
  → m (Mono.MapValue map)
lookupFail err k = Common.maybeFail err . Mono.lookup k

parseTree ∷ String → TTree
parseTree s = Grammar.parseTTree grammar s  
