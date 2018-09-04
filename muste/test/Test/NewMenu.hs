{-# Language UnicodeSyntax, NamedWildCards, TemplateHaskell
  , PartialTypeSignatures, OverloadedStrings, RecordWildCards #-}
-- TODO Still need to add test-case that uses a menu.
-- {-# OPTIONS_GHC -Wall #-}
module Test.NewMenu (tests) where

import Prelude hiding (fail)
import Test.Tasty
import Test.Tasty.HUnit
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Category ((>>>))
import Control.Monad (when)
import Control.Monad.Fail (MonadFail)
import Text.Printf
import qualified Data.Containers as Mono
import Data.Text.Prettyprint.Doc
  ( Pretty, Doc, pretty, nest
  , vsep, (<+>), brackets, enclose, hsep
  )
import Data.Text (Text)
import Data.Function ((&))
import GHC.Exts (fromList, toList)

import Muste (Grammar, TTree, Context)
-- TODO Must test NewFancyMenu in stead.
-- import Muste.Menu.Internal (Menu)
-- import qualified Muste.Menu.Internal as Menu
import qualified Muste.Linearization.Internal as Linearization (ctxtLang)
import Muste.Menu.New (NewFancyMenu, Linearization)
import qualified Muste.Menu.New as Menu
import Muste.Sentence (Token)
import qualified Muste.Sentence.Token as Token
import qualified Muste.Sentence as Sentence
import Muste.Sentence.Annotated (Annotated)
import qualified Muste.Sentence.Annotated as Sentence
import Muste.Sentence.Unannotated (Unannotated)
import qualified Muste.Common as Common
import qualified Muste.Grammar.Internal as Grammar
import qualified Muste.Util as Util

import Test.Common (failDoc, renderDoc)
import qualified Test.Common as Test
import Test.NewMenuTestCases (LinTestCase, linTestCases)

grammar :: Grammar
grammar = Test.grammar

getMenu ∷ TTree → TTree → TTree → NewFancyMenu
getMenu src trg t
  = mkLin src trg t
  & Menu.getNewFancyMenu theCtxt

mkLin ∷ TTree → TTree → TTree → Linearization (Token Annotated)
mkLin src trg t
  = Sentence.annotated theCtxt (error "Don't need the language here") src trg t
  & Sentence.linearization @Annotated

theCtxt ∷ Context
theCtxt = Util.unsafeGetContext grammar "ExemplumSwe"

tests ∷ TestTree
tests = testGroup "NewFancyMenu" $
        map mkTestLinearizations linTestCases

-- | Makes tests for menus based on 'Linearization's (as opposed to
-- 'mkTest' that does it based on the internal syntax for sentences).
mkTestLinearizations ∷ LinTestCase → TestTree
mkTestLinearizations (lang, src, tests) = testGroup src $ map mkTestCase tests
    where ctxt = Util.unsafeGetContext grammar lang
          allMenuItems = getAllSuggestions ctxt src
          mkTestCase (sel, trg)
              = testCase name $
                if null sel then
                    when (not (null testSelections)) $
                    testFailure [ "Expected to *not* find the target."
                                , "But found it here:" <+> hsep (map Menu.prettySelection testSelections)
                                ]
                else if sel `elem` testSelections then
                    when (length testSelections > 1) $
                    testFailure [ "Did find the target in menu:" <+> Menu.prettySelection sel
                                , "But also found it here:" <+> hsep (map Menu.prettySelection testSelections)
                                ]
                else 
                    testFailure [ "Expected to find the target in menu:" <+> Menu.prettySelection sel
                                , if null testSelections
                                  then "But did not find it anywhere"
                                  else "But found it here instead:" <+> hsep (map Menu.prettySelection testSelections)
                                ]
              where testSelections = [ sel' | (sel', item) <- allMenuItems, item == trg ]
                    testFailure explanation = failDoc $ vsep explanation
                    name = src ++ " " ++ show sel ++ " --> " ++ trg


getAllSuggestions ∷ Context → String → [(Menu.Selection, String)]
getAllSuggestions ctxt sent 
    = [ (sel, Sentence.stringRep lin) |
        (sel, items) <- Map.toList mmap,
        (_sel, lin) <- Set.toList items ]
    where mmap = Menu.unNewFancyMenu $ Menu.getMenuItems ctxt sent

prettyTruncate ∷ Pretty a ⇒ Int → Set a → Doc b
prettyTruncate n s = vsep $ [pretty trnc] ++ truncationWarning
  where
  (trnc, rest) = splitAt n $ Set.toList s
  truncationWarning = case null rest of
    False → [pretty @String "...RESULT TRUNCATED..."]
    True  → []
