{-# Language UnicodeSyntax, NamedWildCards, TemplateHaskell #-}
module Test.Menu (tests) where

import Data.Semigroup
import Data.Maybe
import Data.Functor
import Control.Monad (void)
import Test.Tasty
import Test.Tasty.HUnit
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Foldable
import Text.Printf
import qualified Data.Containers as Mono
import Data.ByteString (ByteString)
import qualified Data.ByteString.Lazy as LB
import Data.Text.Prettyprint.Doc (Pretty)
import qualified Data.Text.Prettyprint.Doc as Doc

import Muste.Common
import Muste
import Muste.Menu
import qualified Muste.Tree.Internal as Tree
import qualified Muste.Grammar.Internal as Grammar
import qualified Muste.Menu.Internal as Menu
import qualified Muste.Linearization.Internal as Linearization
import qualified Muste.Grammar.Embed as Embed

resource :: Applicative m ⇒ m Grammar
resource = pure grammar
  where
  g = "novo-modo-test/Prima"
  err = error "Can't find grammar"
  grammar' ∷ (String, ByteString)
  grammar' = $(Embed.grammar "novo_modo/Prima")
  grammar ∷ Grammar
  grammar = Grammar.parseGrammar $ LB.fromStrict $ snd grammar'

ambiguities ∷ Grammar → Assertion
ambiguities grammar = (menu `contains` both) @?= True
  where
  ctxts ∷ Map String Context
  ctxts = Linearization.readLangs grammar
  treeDefinite ∷ TTree
  treeDefinite = parse
    $ "useS (useCl (simpleCl (useCNdefsg   (useN hostis_N)) "
    <>            "(transV vincere_V2 (usePN Africa_PN))))"
  treeIndefinite ∷ TTree
  treeIndefinite = parse
    $ "useS (useCl (simpleCl (useCNindefsg (useN hostis_N)) "
    <>            "(transV vincere_V2 (usePN Africa_PN))))"
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
  menu = getMenu ctxts treeDefinite
  parse ∷ String → TTree
  parse = Grammar.parseTTree grammar

getMenu ∷ Map String Context → TTree → Menu
getMenu ctxts = getCleanMenu latinCtxt
  where
  latinCtxt ∷ Context
  latinCtxt = fromMaybe (error "Can't find Latin context")
    $ Map.lookup "PrimaLat" ctxts

theTests ∷ IO Grammar → TestTree
theTests act = 
  testGroup "Prune"
    [ "ambiguities" |> ambiguities
    ]
  where
  (|>) ∷ TestName → (Grammar → Assertion) → TestTree
  tn |> asrt = testCase tn $ act >>= asrt

tests :: TestTree
tests = withResource resource mempty theTests
