{-# Language TemplateHaskell #-}
module Muste.Grammar.Grammars (grammars) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.ByteString (ByteString)
import qualified Data.ByteString.Lazy as LB

import Muste.Grammar.Internal (Grammar, parseGrammar)
import qualified Muste.Grammar.Embed as Embed

grammars :: Map String Grammar
grammars = Map.fromList (uncurry grm <$> grammars')
  where
  grm :: String -> ByteString -> (String, Grammar)
  grm idf pgf = (idf, parseGrammar $ LB.fromStrict pgf)

grammars' :: [(String, ByteString)]
grammars' =
  [ $(Embed.grammar "novo_modo/Prima")
  , $(Embed.grammar "novo_modo/Secunda")
  , $(Embed.grammar "novo_modo/Tertia")
  , $(Embed.grammar "novo_modo/Quarta")
  ]
