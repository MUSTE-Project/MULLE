{-# Language UnicodeSyntax, NamedWildCards, TemplateHaskell, PartialTypeSignatures #-}
-- TODO Still need to add test-case that uses a menu.
-- {-# OPTIONS_GHC -Wall #-}
module Test.Menu (tests) where

import Prelude hiding (fail)
import Data.Foldable
import Data.Maybe
import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Category ((>>>))
import Control.Monad (when)
import Control.Monad.Fail (MonadFail(fail))
import Text.Printf
import Data.Containers (IsMap)
import qualified Data.Containers as Mono
import Data.Text.Prettyprint.Doc
  (Pretty, Doc, pretty, layoutCompact, nest, vsep, (<+>))
import Data.Text.Prettyprint.Doc.Render.String (renderString)

import Muste (Grammar, TTree, Menu, Linearization, Context, CostTree)
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
theCtxt = unsafeGetContext "ExemplumSwe"

unsafeGetContext ∷ String → Context
unsafeGetContext lang = fromMaybe err $ getCtxt lang
  where
  err = error $ printf "Can't find %s" lang

getCtxt ∷ MonadFail m ⇒ String → m Context
getCtxt lang = lookupFail err lang $ Linearization.readLangs grammar
  where
  err = printf "Can't find %s" lang


-- | Checks that the
tests ∷ TestTree
tests = testGroup "Menu" [menuLin, menuTrees]

menuLin ∷ TestTree
menuLin = testGroup "Linearization" $ mkTest' <$>
  [ ("REPL: fienden" , "ExemplumSwe", "fienden besegrar Afrika", [0], "en fiende besegrar Afrika")
  , ("REPL: fienden", "ExemplumSwe", "fienden besegrar Afrika", [0], "Augustus besegrar Afrika")
  , ("REPL: besegrar", "ExemplumSwe", "fienden besegrar Afrika", [1], "fienden är Afrika")
  , ("REPL: Afrika", "ExemplumSwe", "fienden är Afrika", [2], "fienden är stor")
  , ("REPL: Afrika", "ExemplumSwe", "fienden är Afrika", [2], "fienden är en vän")
  , ("DEL: det besegrade", "ExemplumSwe", "det besegrade riket är stort", [0,1], "fienden besegrar Afrika")
    -- NOTE: the "selection" should really be an insertion BEFORE "fienden" -- how do we represent that?
  , ("INS: det besegrade", "ExemplumSwe", "fienden besegrar Afrika", [], "det besegrade riket är stort")
  ]

mkTest' ∷ (String, String, String, [Int], String) → TestTree
mkTest' (nm, lang, src, sel, trg) = testCase nm $ do
  sg ← getSuggestions src (Selection.fromList sel)
  let trgL = parseLin trg
  when (not $ Set.null (Set.intersection @Linearization sg trgL))
    (failDoc $ nest 2 $ vsep
      [ pretty @String "Expected to find one of:"
      , prettyTruncate 8 trgL
      , pretty @String "Somewhere in:"
      , prettyTruncate 8 sg
      ]
    )
  where
  ctxt ∷ Context
  ctxt = unsafeGetContext lang
  mkL ∷ TTree → Linearization
  mkL = mkLinSimpl ctxt
  parseLin ∷ String → Set Linearization
  parseLin = parseTree >>> map mkL >>> Set.fromList
  parseTree ∷ String → [TTree]
  parseTree = Grammar.parseSentence grammar (Linearization.ctxtLang ctxt)
  getM ∷ String → Menu
  getM = foldMap (Menu.getMenu ctxt) . parseLin
  getSuggestions ∷ MonadFail m ⇒ String → Selection → m (Set Linearization)
  getSuggestions s sl = Set.fromList . map Menu.lin
    <$> lookupFail (err s) sl (getM s)
  err ∷ String → String
  err = printf "Selection not found in menu for: \"%s\""

prettyTruncate ∷ Pretty a ⇒ Int → Set a → Doc b
prettyTruncate n s = vsep [truncationWarning, pretty trnc]
  where
  (trnc, rest) = splitAt n $ Set.toList s
  truncationWarning = case null rest of
    False → pretty @String "[RESULT TRUNCATED]:"
    True → mempty

failDoc ∷ MonadFail m ⇒ Doc a → m ()
failDoc = fail . renderString . layoutCompact
  
mkLinSimpl ∷ Context → TTree → Linearization
mkLinSimpl c t = Linearization.mkLin c t t t

menuTrees :: TestTree
menuTrees = testGroup "Trees" $ mkTests
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
