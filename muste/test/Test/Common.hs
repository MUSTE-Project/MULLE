{-# Language TemplateHaskell #-}
module Test.Common (grammar, treeDefinite, treeIndefinite) where

import Muste.Grammar (Grammar)
import qualified Muste.Grammar.Internal as Grammar
import qualified Muste.Grammar.Embed as Embed
import Data.ByteString (ByteString)
import qualified Data.ByteString.Lazy as LB

import Muste (TTree)
import Muste.Grammar.TH (tree)

grammar :: Grammar
grammar = Grammar.parseGrammar $ LB.fromStrict $ snd grammar'
  where
  grammar' ∷ (String, ByteString)
  grammar' = $(Embed.grammar "novo_modo/Exemplum")

treeIndefinite ∷ TTree
treeIndefinite = $(tree "novo_modo/Exemplum"
  $ "(useS (useCl (simpleCl (detCN aSg_Det (useN hostis_N))"
  <>            "(transV vincere_V (usePN Africa_PN)))))")

treeDefinite ∷ TTree
treeDefinite = $(tree "novo_modo/Exemplum"
  $  "(useS (useCl (simpleCl "
  <>   "(detCN theSg_Det (useN hostis_N)) "
  <>   "(transV vincere_V (usePN Africa_PN)))))")
