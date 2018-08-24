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
  ( Pretty, Doc, pretty, layoutCompact, nest
  , vsep, sep, (<+>), brackets, enclose
  )

import Muste (Grammar, TTree, Menu, Linearization, Context, CostTree)
import qualified Muste
import qualified Muste.Common as Common
import qualified Muste.Grammar.Internal as Grammar
import qualified Muste.Linearization.Internal as Linearization
import qualified Muste.Menu.Internal as Menu
import Muste.Selection (Selection)
import qualified Muste.Selection as Selection
import qualified Muste.Util as Util

import Muste.Common (prettyShow)
import Test.Common (failDoc, renderDoc)
import qualified Test.Common as Test

grammar :: Grammar
grammar = Test.grammar

getMenu ∷ TTree → TTree → TTree → Menu
getMenu src trg = mkLin src trg >>> Muste.getMenu theCtxt

mkLin ∷ TTree → TTree → TTree → Linearization
mkLin src trg = Linearization.mkLin theCtxt src trg

theCtxt ∷ Context
theCtxt = Util.unsafeGetContext grammar "ExemplumSwe"

-- | Checks that the
tests ∷ TestTree
tests = testGroup "Menu" [menuLin, menuTrees]

-- | A test-case consists of the following (in order of appearance):
--
-- * A helpful name for the test-case.
-- * The language that the two sentences are written in.
-- * The sentence to get suggestions from.
-- * The "selection" to make.
-- * A sentence to (alt.: not) expect to be at this position in the
--   menu.
-- * Whether to expect the sentence to be amongst the suggestions, or
--   expect it *not* to be there.
type LinTestCase = (String, String, String, [Int], String, Bool)

menuLin ∷ TestTree
menuLin = testGroup "Linearization" $ mkTestLinearizations <$>
  [ ("kungen->en kung", "ExemplumSwe", "kungen älskar Paris"     , [0]  , "en kung älskar Paris"     , expectSuccess) -- FAIL
  , ("kungen->Johan"  , "ExemplumSwe", "kungen älskar Paris"     , [0]  , "Johan älskar Paris"       , expectSuccess)
  , ("älskar->är"     , "ExemplumSwe", "kungen älskar Paris"     , [1]  , "kungen är Paris"          , expectSuccess)
  , ("kungen->huset"  , "ExemplumSwe", "kungen är stor"          , [0]  , "huset är stort"           , expectSuccess) 
  , ("Paris->stor"    , "ExemplumSwe", "kungen är Paris"         , [2]  , "kungen är stor"           , expectSuccess)  -- FAIL
  , ("Paris->en vän"  , "ExemplumSwe", "kungen är Paris"         , [2]  , "kungen är en vän"         , expectSuccess)
  , ("DEL: det kalla" , "ExemplumSwe", "det kalla huset är stort", [0,1], "huset är stort"           , expectSuccess)  -- FAIL
    -- NOTE: the "selection" should really be an insertion BEFORE "fienden" -- how do we represent that?
  , ("INS: det kalla" , "ExemplumSwe", "huset är stort"          , []   , "det kalla huset är stort" , expectSuccess)  -- FAIL
  , ("Johan->en kung" , "ExemplumSwe", "Johan älskar Paris"      , [0]  , "en kung älskar Paris"     , expectSuccess)
  , ("INS: stor"      , "ExemplumSwe", "en kung älskar Paris"    , []   , "en stor kung älskar Paris", expectSuccess)  -- FAIL
  , ("Joh.->en st. k.", "ExemplumSwe", "Johan älskar Paris"      , [0]  , "en stor kung älskar Paris", expectFailure)
  ]
  where
  expectSuccess = True
  expectFailure = False

-- | Makes tests for menus based on 'Linearization's (as opposed to
-- 'mkTest' that does it based on the internal syntax for sentences).
mkTestLinearizations ∷ LinTestCase → TestTree
mkTestLinearizations (nm, lang, src, sel, trg, isExpected)
  -- Create a test-case with the given name.
  = testCase nm $ do
    -- Look up suggestions for source tree.  Convert results to their
    -- string-representation.
    sg ← Set.map Linearization.stringRep
      <$> getSuggestions ctxt src (Selection.fromList sel)
    -- Get the string representation of the target.  We could just use
    -- the argument passed in, but this also ensures that the grammar
    -- understands the sentence.  Note that ambiguities may be
    -- introduced here, so this returns a set.
    let trgL = Set.map Linearization.stringRep
          $ parseLin ctxt trg
    -- Some tests are negative tests.  'expecter' reflects this.
        expecter = if isExpected then id else not
    -- This is where you need to "holde tungen like i munden".  We
    -- test the interesection of the suggestions with the (alt.: not-)
    -- expected result.  If the interesection is empty ('null') then
    -- this is an error (alt.: a success).  However!  The following
    -- statement will throw when the condition is *met*.
    when (expecter $ Set.null (Set.intersection @String sg trgL))
    -- Just some pretty-printing of the expected behaviour (shown on
    -- failure).  'failDoc' is a helper that 'throw's and
    -- pretty-prints some pretty-printable stuff in that case.
      (failDoc $ nest 2 $ vsep
        [ pretty @String $ "Testing: [" <> src <> "]  -->  [" <> trg <> "]"
        , pretty " "
        , pretty @String $ "Expected to " <> (if isExpected then "" else "*not* ") <> "find one of:"
        , prettyTruncate limit trgL
        , pretty " "
        , pretty @String "Somewhere in the menu:"
        , prettyTruncate limit sg
        , pretty " "
        ]
      )
    where
    ctxt ∷ Context
    ctxt = Util.unsafeGetContext grammar lang
    limit = maxBound

getSuggestions
  ∷ MonadFail m
  ⇒ Context
  → String
  → Selection
  → m (Set Linearization)
getSuggestions ctxt s sl = Set.fromList . map Menu.lin
  <$> Common.lookupFail err sl mn
  where
  mn = Menu.getMenuFromStringRep ctxt s
  err ∷ String
  err = renderDoc
    $ vsep
      -- [ pretty @String (printf "Selection (%s) not found in menu for: \"%s\"" sl s)
      [ pretty @String "Selection" <+> brackets (pretty sl) <+> pretty @String "not found in menu for:" <+> quotes (pretty @String s)
      , pretty @String "Available selections:"
      , pretty @[Selection] $ Mono.keys mn
      ]
  quotes = enclose (pretty @String "\"") (pretty @String "\"")

parseLin ∷ Context → String → Set Linearization
parseLin ctxt = parseTree >>> map mkL >>> Set.fromList
  where
  parseTree ∷ String → [TTree]
  parseTree = Grammar.parseSentence grammar (Linearization.ctxtLang ctxt)
  mkL ∷ TTree → Linearization
  mkL = Linearization.mkLinSimpl ctxt

prettyTruncate ∷ Pretty a ⇒ Int → Set a → Doc b
prettyTruncate n s = vsep $ [pretty trnc] ++ truncationWarning
  where
  (trnc, rest) = splitAt n $ Set.toList s
  truncationWarning = case null rest of
    False → [pretty @String "...RESULT TRUNCATED..."]
    True  → []

menuTrees :: TestTree
menuTrees = testGroup "Trees" $ mkTests
  [ -- ("name", "source tree", [0], "target tree")
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
    <$> Common.lookupFail s n mn
  err ∷ String
  err = printf "Test.Menu.assertThere: Selection not in tree: (%s)"
    $ show $ pretty n

parseTree ∷ String → TTree
parseTree s = Grammar.parseTTree grammar s  
