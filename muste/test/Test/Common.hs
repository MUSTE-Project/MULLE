{-# Language TemplateHaskell #-}
module Test.Common (grammar) where

import Muste.Grammar (Grammar)
import qualified Muste.Grammar.Internal as Grammar
import qualified Muste.Grammar.Embed as Embed
import Data.ByteString (ByteString)
import qualified Data.ByteString.Lazy as LB

grammar :: Grammar
grammar = Grammar.parseGrammar $ LB.fromStrict $ snd grammar'
  where
  grammar' ∷ (String, ByteString)
  grammar' = $(Embed.grammar "novo_modo/Exemplum")
