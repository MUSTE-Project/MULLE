{-# OPTIONS_GHC -Wall #-}
{-# Language TemplateHaskell #-}
module Test.Prune (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Set as Set
import Data.Foldable
import Data.Set (Set)
import Control.Monad

import Muste
import Muste.Prune
import qualified Test.Common as Test
import qualified Muste.Grammar.Internal as Grammar
import Data.Text.Prettyprint.Doc (pretty, vsep)

import Test.Common (failDoc)

-- | Consists of a
--
-- * Name
-- * A tree to expect in the suggestions
-- * A tree to *not* expect in the suggestions
type PruneTest = (String, String, String, String)

-- | Issue #5: Should not include results that can be reached in
-- multiple steps E.g. the suggestions for
--
--     usePN Africa_PN
--
-- Should not include
--
--     useCNdefsg (attribCN (useA victus_A) (useN imperium_N))
--
-- Since it can be reached via:
--
--     useCNdefsg (useN imperium_N)
--
tests ∷ TestTree
tests = testGroup "Prune" $ mkTest <$>
  [ ("Africa -> imperium -> magnum imperium",
     "useS (useCl (simpleCl (usePN john_PN)                                          (transV love_V (usePN paris_PN))))",
     "useS (useCl (simpleCl (detCN aSg_Det                         (useN friend_N))  (transV love_V (usePN paris_PN))))",
     "useS (useCl (simpleCl (detCN aSg_Det (attribCN (useA good_A) (useN friend_N))) (transV love_V (usePN paris_PN))))")
  ]
  -- [ isSuggested    short
  -- , isNotSuggested long
  -- ]
  where
  mkTest ∷ PruneTest → TestTree
  mkTest (nm, src, ex, nEx) = testCase nm $ do
    let trees = replacements $ parse src
        expect ∷ Bool → TTree → Assertion
        expect b t = when (expecter $ t `elem` trees) $ failDoc $ vsep
          [ pretty @String "This tree:"
          , pretty t
          , pretty @String $ "was " <> (if b then "not " else "") <> "found in any of the suggestions:"
          , pretty $ Set.toList trees
          ]
          where expecter = if b then not else id
    expect True $ parse ex
    expect False $ parse nEx

-- parseTTree :: Grammar -> String -> TTree
parse ∷ String → TTree
parse = Grammar.parseTTree grammar

grammar :: Grammar
grammar = Test.grammar

replacements ∷ TTree → Set TTree
replacements source = fold ts
  where
  g     = Test.grammar
  adjTs = getAdjunctionTrees g
  m     = replaceTrees g adjTs source
  ts    = Set.map snd <$> m
