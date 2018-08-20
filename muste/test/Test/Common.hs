{-# Language TemplateHaskell #-}
module Test.Common (prima) where

import Muste.Grammar (Grammar)
import qualified Muste.Grammar.Internal as Grammar
import qualified Muste.Grammar.Embed as Embed
import Data.ByteString (ByteString)
import qualified Data.ByteString.Lazy as LB

prima :: Grammar
prima = Grammar.parseGrammar $ LB.fromStrict $ snd grammar'
  where
  grammar' ∷ (String, ByteString)
  grammar' = $(Embed.grammar "novo_modo/Exemplum")
