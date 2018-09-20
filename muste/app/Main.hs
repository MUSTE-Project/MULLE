{-# OPTIONS_GHC -Wall #-}
{-# Language RecordWildCards, NamedFieldPuns, TemplateHaskell,
  DeriveAnyClass, OverloadedStrings, MultiParamTypeClasses,
  DerivingStrategies #-}
module Main (main) where

import Muste.Prelude

import Data.ByteString (ByteString)
import qualified Muste.Grammar.Embed    as Embed
import Data.String.Conversions (convertString)

import Muste (Grammar, BuilderInfo(..), Context)
import qualified Muste.Util             as Muste
import qualified Muste.Grammar.Internal as Grammar

import Options (Options(Options))
import qualified Options
import qualified Muste.Repl             as Repl

grammar :: Grammar
grammar = Grammar.parseGrammar $ convertString $ snd grammar'
  where
  grammar' ∷ (Text, ByteString)
  grammar' = $(Embed.grammar "novo_modo/Exemplum")

makeEnv ∷ Options → Repl.Env
makeEnv opts@(Options{..}) = Repl.Env defLang c
  where
  c ∷ Context
  c = Muste.unsafeGetContext (builderInfo opts) grammar language

defLang ∷ String
defLang = "Swe"

builderInfo ∷ Options → BuilderInfo
builderInfo Options{..} = BuilderInfo { searchDepth }

main :: IO ()
main = do
  opts ← Options.getOptions
  let e ∷ Repl.Env
      e = makeEnv opts
  let sentences ∷ [String]
      sentences = Options.sentences opts
      replOpts ∷ Repl.Options
      replOpts = Repl.Options $ Options.printNodes opts
  -- If there are any sentences supplied on the command line, run them
  -- all.
  void $ Repl.detachedly replOpts e (traverse Repl.updateMenu sentences)
  -- If we are also in interactive mode, start the interactive session.
  when (Options.interactiveMode opts)
    $ Repl.interactively replOpts e Repl.updateMenu
