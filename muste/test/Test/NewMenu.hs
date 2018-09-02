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

grammar :: Grammar
grammar = Test.grammar

getMenu ∷ TTree → TTree → TTree → NewFancyMenu
-- getMenu src trg = mkLin src trg >>> Menu.getMenu theCtxt
getMenu src trg t
  = mkLin src trg t
  & Menu.getNewFancyMenu theCtxt
  --mkLin src trg >>> _ Menu.getNewFancyMenu theCtxt

mkLin ∷ TTree → TTree → TTree → Linearization (Token Annotated)
mkLin src trg t
  = Sentence.annotated theCtxt (error "Don't need the language here") src trg t
  & Sentence.linearization @Annotated

-- mkLin ∷ TTree → TTree → TTree → Linearization
-- mkLin src trg = Linearization.mkLin theCtxt src trg

theCtxt ∷ Context
theCtxt = Util.unsafeGetContext grammar "ExemplumSwe"

-- | Checks that the
tests ∷ TestTree
tests = testGroup "NewFancyMenu" [menuLin]

-- | A test-case consists of the following (in order of appearance):
--
-- * The language that the two sentences are written in.
-- * The sentence to get suggestions from.
-- * A helpful name for the test-case.
-- * The "selection" to make. If the selection is [] then the test is supposed to fail.
-- * A sentence to (alt.: not) expect to be at this position in the menu.
type LinTestCase = (Text, String, [(String, Menu.Selection, String)])

linTestCases :: [LinTestCase]
linTestCases = [ ("ExemplumSwe", "kungen älskar Paris",
                  [ ("kungen->en kung", [(0,0)], "en kung älskar Paris")
                  , ("kungen->Johan"  , [(0,1)], "Johan älskar Paris")
                  , ("älskar->är"     , [(1,2)], "kungen är Paris")
                  ])
               , ("ExemplumSwe", "kungen är stor",
                  [ ("kungen->huset"  , [(0,1)], "huset är stort")
                  ])
               , ("ExemplumSwe", "kungen är Paris",
                  [ ("Paris->stor"    , [(2,3)], "kungen är stor")
                  , ("Paris->en vän"  , [(2,3)], "kungen är en vän")
                  ])
               , ("ExemplumSwe", "det kalla huset är stort",
                  [ ("DEL: det kalla" , [(0,2)], "huset är stort")
                  ])
               , ("ExemplumSwe", "huset är stort",
                  [ ("INS: det kalla"  , [(0,0)], "det kalla huset är stort")
                  ])
               , ("ExemplumSwe", "Johan älskar Paris",
                  [ ("Johan->en kung" , [(0,1)], "en kung älskar Paris")
                  , ("NOT: Johan->en stor kung", [], "en stor kung älskar Paris")
                  ])
               , ("ExemplumSwe", "en kung älskar Paris",
                  [ ("INS: stor"      , [(1,1)], "en stor kung älskar Paris")
                  ])
               , ("ExemplumSwe", "Johan älskar vännen",
                  [ ("INS: idag"      , [(3,3)], "Johan älskar vännen idag")
                  , ("INS: i Paris"   , [(3,3)], "Johan älskar vännen i Paris")
                  ])
               , ("ExemplumSwe", "Johan älskar vännen idag",
                  [ ("DEL: idag"      , [(3,4)], "Johan älskar vännen")
                  ])
               , ("ExemplumSwe", "Johan älskar vännen i Paris",
                  [ ("DEL: i Paris"   , [(3,5)], "Johan älskar vännen")
                  ])
               ]


menuLin ∷ TestTree
menuLin = testGroup "Linearization" $ concatMap mkTestLinearizations linTestCases

-- | Makes tests for menus based on 'Linearization's (as opposed to
-- 'mkTest' that does it based on the internal syntax for sentences).
mkTestLinearizations ∷ LinTestCase → [TestTree]
mkTestLinearizations (lang, src, tests) = map mkTestCase tests
    where ctxt = Util.unsafeGetContext grammar lang
          allMenuItems = getAllSuggestions ctxt src
          mkTestCase (name, sel, trg)
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
                    testFailure explanation = failDoc $ nest 2 $ vsep
                                              [ pretty @String $ "Testing: [" <> src <> "]  -->  [" <> trg <> "]"
                                              , vsep explanation
                                              , " "
                                              ]


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
