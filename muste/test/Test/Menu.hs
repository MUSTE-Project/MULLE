{-# Language UnicodeSyntax, NamedWildCards, TemplateHaskell
  , PartialTypeSignatures, OverloadedStrings, RecordWildCards #-}
{-# OPTIONS_GHC -Wall -Wno-unused-top-binds #-}
module Test.Menu (tests) where

import Prelude ()
import Muste.Prelude

import Test.Tasty
import Test.Tasty.HUnit
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Text.Prettyprint.Doc
  ( Pretty, Doc, pretty , vsep, (<+>), hsep
  )

import Muste (Grammar, TTree, Context)
import Muste.Menu.Internal (Menu, Linearization)
import qualified Muste.Menu.Internal as Menu
import Muste.Sentence (Token)
import qualified Muste.Sentence as Sentence
import Muste.Sentence.Annotated (Annotated)
import qualified Muste.Sentence.Annotated as Sentence
import qualified Muste.Util as Util

import Test.Common (failDoc)
import qualified Test.Common as Test
import Test.Menu.TestCases (LinTestCase, linTestCases)

grammar :: Grammar
grammar = Test.grammar

getMenu ∷ TTree → TTree → TTree → Menu
getMenu src trg t
  = mkLin src trg t
  & Menu.getMenu theCtxt

mkLin ∷ TTree → TTree → TTree → Linearization (Token Annotated)
mkLin src trg t
  = Sentence.annotated theCtxt (error "Don't need the language here") src trg t
  & Sentence.linearization @Annotated

theCtxt ∷ Context
theCtxt = Util.unsafeGetContext grammar "ExemplumSwe"

tests ∷ TestTree
tests = testGroup "Menu" $
        map mkTestLinearizations linTestCases

-- | Makes tests for menus based on 'Linearization's (as opposed to
-- 'mkTest' that does it based on the internal syntax for sentences).
mkTestLinearizations ∷ LinTestCase → TestTree
mkTestLinearizations (lang, src, theTests) = testGroup src $ map mkTestCase theTests
    where ctxt = Util.unsafeGetContext grammar lang
          allMenuItems = getAllSuggestions ctxt src
          mkTestCase ∷ (Menu.Selection, String) → TestTree
          mkTestCase (sel, trg)
              = testCase name $
                if null $ toList sel then
                    when (not (null testSelections)) $
                    testFailure [ "Expected to *not* find the target."
                                , "But found it here:" <+> hsep (map pretty testSelections)
                                ]
                else if sel `elem` testSelections then
                    when (length testSelections > 1) $
                    testFailure [ "Did find the target in menu:" <+> pretty sel
                                , "But also found it here:" <+> hsep (map pretty testSelections)
                                ]
                else 
                    testFailure [ "Expected to find the target in menu:" <+> pretty sel
                                , if null testSelections
                                  then "But did not find it anywhere"
                                  else "But found it here instead:" <+> hsep (map pretty testSelections)
                                ]
              where testSelections = [ sel' | (sel', item) <- allMenuItems, item == trg ]
                    testFailure explanation = failDoc $ vsep explanation
                    name = src ++ " " ++ prettyShow sel ++ " --> " ++ trg

prettyShow ∷ Pretty a ⇒ a → String
prettyShow = show . pretty

getAllSuggestions ∷ Context → String → [(Menu.Selection, String)]
getAllSuggestions ctxt sent 
    = [ (sel, Sentence.stringRep lin) |
        (sel, items) <- Map.toList mmap,
        (_sel, lin) <- Set.toList items ]
    where mmap = Menu.unMenu $ Menu.getMenuItems ctxt sent

prettyTruncate ∷ Pretty a ⇒ Int → Set a → Doc b
prettyTruncate n s = vsep $ [pretty trnc] ++ truncationWarning
  where
  (trnc, rest) = splitAt n $ Set.toList s
  truncationWarning = case null rest of
    False → [pretty @String "...RESULT TRUNCATED..."]
    True  → []
