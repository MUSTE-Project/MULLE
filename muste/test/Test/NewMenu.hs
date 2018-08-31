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
import Control.Category ((>>>))
import Control.Monad (when)
import Control.Monad.Fail (MonadFail)
import Text.Printf
import qualified Data.Containers as Mono
import Data.Text.Prettyprint.Doc
  ( Pretty, Doc, pretty, nest
  , vsep, (<+>), brackets, enclose
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
tests = testGroup "NewFancyMenu" [menuLin, menuTrees]

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
type LinTestCase = (String, Text, String, Menu.Selection, String, Bool)

menuLin ∷ TestTree
menuLin = testGroup "Linearization" $ mkTestLinearizations <$>
  [ ("kungen->en kung", "ExemplumSwe", "kungen älskar Paris"        , [(0,0)]
    , "en kung älskar Paris"       , expectSuccess)  -- FAIL
  , ("kungen->Johan"  , "ExemplumSwe", "kungen älskar Paris"        , [(0,0)]
    , "Johan älskar Paris"         , expectSuccess)
  , ("älskar->är"     , "ExemplumSwe", "kungen älskar Paris"        , [(1,1)]
    , "kungen är Paris"            , expectSuccess)
  , ("kungen->huset"  , "ExemplumSwe", "kungen är stor"             , [(0,0)]
    , "huset är stort"             , expectSuccess)
  , ("Paris->stor"    , "ExemplumSwe", "kungen är Paris"            , [(2,2)]
    , "kungen är stor"             , expectSuccess)  -- FAIL
  , ("Paris->en vän"  , "ExemplumSwe", "kungen är Paris"            , [(2,2)]
    , "kungen är en vän"           , expectSuccess)
  , ("DEL: det kalla" , "ExemplumSwe", "det kalla huset är stort"   , [(0,0),(1,1)]
    , "huset är stort"             , expectSuccess)  -- FAIL
    -- NOTE: the "selection" should really be an insertion BEFORE "fienden" -- how do we represent that?
  , ("INS: det kalla" , "ExemplumSwe", "huset är stort"             , []
    , "det kalla huset är stort"   , expectSuccess)  -- FAIL
  , ("Johan->en kung" , "ExemplumSwe", "Johan älskar Paris"         , [(0,0)]
    , "en kung älskar Paris"       , expectSuccess)
  , ("INS: stor"      , "ExemplumSwe", "en kung älskar Paris"       , []
    , "en stor kung älskar Paris"  , expectSuccess)  -- FAIL
  , ("Joh.->en st. k.", "ExemplumSwe", "Johan älskar Paris"         , [(0,0)]
    , "en stor kung älskar Paris"  , expectFailure)
  , ("INS: idag"      , "ExemplumSwe", "Johan älskar vännen"        , []
    , "Johan älskar vännen idag"   , expectSuccess)  -- FAIL
  , ("INS: i Paris"   , "ExemplumSwe", "Johan älskar vännen"        , []
    , "Johan älskar vännen i Paris", expectSuccess)  -- FAIL
  , ("DEL: idag"      , "ExemplumSwe", "Johan älskar vännen idag"   , [(3,3)]
    , "Johan älskar vännen"        , expectSuccess)  -- FAIL
  , ("DEL: i Paris"   , "ExemplumSwe", "Johan älskar vännen i Paris", [(3,3),(4,4)]
    , "Johan älskar vännen"        , expectSuccess)  -- FAIL
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
    sg ← Set.map Sentence.stringRep
      <$> getSuggestions ctxt src sel
    -- Get the string representation of the target.  We could just use
    -- the argument passed in, but this also ensures that the grammar
    -- understands the sentence.  Note that ambiguities may be
    -- introduced here, so this returns a set.
    let trgL = Set.map Sentence.stringRep
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
        , pretty @String " "
        , pretty @String $ "Expected to " <> (if isExpected then "" else "*not* ") <> "find one of:"
        , prettyTruncate limit trgL
        , pretty @String " "
        , pretty @String "Somewhere in the menu:"
        , prettyTruncate limit sg
        , pretty @String " "
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
  → Menu.Selection
  → m (Set (Linearization (Sentence.Token Unannotated)))
-- getSuggestions ctxt s sl = Set.fromList . map Menu.lin
-- getSuggestions ctxt s sl = Set.fromList . map (Sentence.linearization . undefined)
getSuggestions ctxt s sl = Set.map snd
  <$> Common.lookupFail err sl mn
  where
  mn ∷ NewFancyMenu
  mn = Menu.getMenuItems ctxt s
  err ∷ String
  err = renderDoc
    $ vsep
      -- [ pretty @String (printf "Selection (%s) not found in menu for: \"%s\"" sl s)
      [ pretty @String "Selection" <+> brackets (pretty sl) <+> pretty @String "not found in menu for:" <+> quotes (pretty @String s)
      , pretty @String "Available selections:"
      , pretty @[Menu.Selection] $ Mono.keys mn
      ]
  quotes = enclose (pretty @String "\"") (pretty @String "\"")

parseLin ∷ Context → String → Set (Linearization (Token Annotated))
parseLin ctxt
  = parseTree'
  >>> map (Sentence.linearization . mkL)
  >>> Set.fromList
  where
  l = Linearization.ctxtLang ctxt
  parseTree' ∷ String → [TTree]
  parseTree' = Grammar.parseSentence grammar l
  -- parseTree' = Grammar.parseSentence grammar (_ ctxt)
  -- parseTree' = Sentence.disambiguate ctxt . fromString
  mkL ∷ TTree → Annotated
  -- mkL = Linearization.mkLinSimpl ctxt
  mkL t = Sentence.annotated ctxt (error "Don't need the language here") t t t

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

mkTests ∷ [(String, String, Menu.Selection, String)] → [TestTree]
mkTests = map go
  where
  go ∷ (String, String, Menu.Selection, String) → TestTree
  go (nm, src, n, trg) = testCase nm
    $ assertThere (parseTree src) n (parseTree trg)

forgetAnnotation
  ∷ Linearization (Token Annotated) → Linearization (Token Unannotated)
forgetAnnotation = fromList . map step . toList
  where
  step ∷ Token.Annotated → Token.Unannotated
  step (Token.Annotated a _) = Token.Unannotated a

-- | @'assertThere' src n trg@ asserts that @trg@ exists in the menu
-- you get from @src@.
assertThere ∷ TTree → Menu.Selection → TTree → Assertion
assertThere src n trg = do
  cts ← lookupMenu err (getMenu src trg src)
  Mono.member (forgetAnnotation $ mkLin src trg trg) cts @?= True
  -- Mono.member undefined cts @?= True
  where
  lookupMenu
    ∷ ∀ m
    . MonadFail m
    ⇒ String
    → NewFancyMenu
    → m (Set (Linearization (Token Unannotated)))
  lookupMenu s mn
    =   Set.map (snd)
    <$> Common.lookupFail s n mn
  err ∷ String
  err = printf "Test.Menu.assertThere: Selection not in tree: (%s)"
    $ show $ pretty n

parseTree ∷ String → TTree
parseTree s = Grammar.parseTTree grammar s  
