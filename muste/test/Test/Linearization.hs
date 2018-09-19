{-# Language UnicodeSyntax, NamedWildCards, OverloadedStrings #-}
module Test.Linearization (tests) where

import Prelude ()
import Muste.Prelude
import Test.Tasty
import Test.Tasty.HUnit
import Data.Map (Map)
import qualified Data.Map as Map

import Muste (Grammar, Context, TTree, Linearization)
import qualified Muste.Linearization.Internal as Linearization
import qualified Muste.Grammar.Internal as Grammar

import qualified Test.Common as Test

grammar :: Grammar
grammar = Test.grammar

ctxts ∷ Map Text Context
ctxts = Linearization.readLangs grammar

ambiguities ∷ Assertion
ambiguities = treeDefiniteL @?= treeIndefiniteL

treeDefiniteL ∷ Linearization
treeDefiniteL = mkLin Test.treeDefinite

treeIndefiniteL ∷ Linearization
treeIndefiniteL = mkLin Test.treeIndefinite

latCtxt ∷ Context
latCtxt = fromMaybe (error "Can't find Latin context")
  $ Map.lookup "ExemplumLat" ctxts

mkLin ∷ TTree → Linearization
mkLin = Linearization.mkLin theCtxt Test.treeDefinite Test.treeIndefinite

theCtxt ∷ Context
theCtxt = latCtxt

isAmbiguous :: String -> Assertion
isAmbiguous sent
  = length (parseSentence theCtxt sent)
  > 1 @? show (parseSentence theCtxt sent)

parseSentence ∷ Context -> String → [TTree]
parseSentence ctxt = Grammar.parseSentence grammar (Linearization.ctxtLang ctxt)

tests ∷ TestTree
tests =
  testGroup "Linearization"
    [ "The (in-)definite form in latin is ambiguous" |> ambiguities
    , "The (in-)definite form in latin is ambiguous (v2)" |> isAmbiguous "amicus Lutetiam amat"
    ]
  where
  (|>) = testCase
