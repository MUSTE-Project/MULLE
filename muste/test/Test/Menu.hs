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
import Muste (Grammar, Context, TTree, Menu)
import qualified Muste as Muste
import qualified Muste.Grammar.Internal as Grammar
import qualified Muste.Menu.Internal as Menu
import qualified Muste.Linearization.Internal as Linearization
import qualified Muste.Grammar.Embed as Embed

grammar :: Grammar
grammar = Grammar.parseGrammar $ LB.fromStrict $ snd grammar'
  where
  grammar' ∷ (String, ByteString)
  grammar' = $(Embed.grammar "novo_modo/Prima")

ctxts ∷ Map String Context
ctxts = Linearization.readLangs grammar

ambiguities ∷ Assertion
ambiguities = (menu `contains` both) @?= True
  where
  both ∷ [TTree]
  both = [treeDefinite, treeIndefinite]
  contains ∷ Menu → [TTree] → Bool
  contains mn ts
    = contains' ts
    $ groupsOfTrees mn
  groupsOfTrees ∷ Menu → [[TTree]]
  groupsOfTrees mn
    = map (Set.toList . Menu.trees)
    $ fromMaybe (error "Path not found")
    $ Mono.lookup [0,0,0] mn
  contains' ∷ [TTree] → [[TTree]] → Bool
  contains' ts = any (isSubListOf ts)
  menu = getMenu treeDefinite

treeDefinite ∷ TTree
treeDefinite = parse
  $ "useS (useCl (simpleCl (useCNdefsg   (useN hostis_N)) "
  <>            "(transV vincere_V2 (usePN Africa_PN))))"

treeIndefinite ∷ TTree
treeIndefinite = parse
  $ "useS (useCl (simpleCl (useCNindefsg (useN hostis_N)) "
  <>            "(transV vincere_V2 (usePN Africa_PN))))"

parse ∷ String → TTree
parse = Grammar.parseTTree grammar

getMenu ∷ TTree → Menu
getMenu = Muste.getCleanMenu latinCtxt
  where
  latinCtxt ∷ Context
  latinCtxt = fromMaybe (error "Can't find Latin context")
    $ Map.lookup "PrimaLat" ctxts

tests ∷ TestTree
tests =
  testGroup "Prune"
    [ "ambiguities" |> ambiguities
    ]
  where
  (|>) = testCase
