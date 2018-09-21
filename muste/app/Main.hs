{-# OPTIONS_GHC -Wall #-}
{-# Language RecordWildCards, NamedFieldPuns, TemplateHaskell,
  DeriveAnyClass, OverloadedStrings, MultiParamTypeClasses,
  DerivingStrategies #-}
module Main (main) where

import Muste.Prelude

import Muste (Grammar, Context)
import qualified Muste.Util             as Muste
import qualified Muste.Grammar.Internal as Grammar
import Muste.AdjunctionTrees (BuilderInfo(..))
import qualified Muste.Menu as Menu

import Options (Options(Options))
import qualified Options
import qualified Muste.Repl             as Repl

makeEnv ∷ Options → Repl.Env
makeEnv opts@(Options{..}) = Repl.Env language c
  where
  g ∷ Grammar
  g = fromMaybe (error "Grammar not found") $ Grammar.lookupGrammar grammar
  c ∷ Context
  c = Muste.unsafeGetContext (builderInfo opts) g grammarLang

builderInfo ∷ Options → BuilderInfo
builderInfo Options{..} = BuilderInfo { searchDepth }

main :: IO ()
main = do
  opts@Options{..} ← Options.getOptions
  let pruneOpts ∷ Menu.PruneOpts
      pruneOpts = Menu.PruneOpts pruneSearchDepth
      e ∷ Repl.Env
      e = makeEnv opts
      replOpts ∷ Repl.Options
      replOpts = Repl.Options printNodes printCompact pruneOpts
  -- If there are any sentences supplied on the command line, run them
  -- all.
  void $ Repl.detachedly replOpts e (traverse Repl.updateMenu sentences)
  -- If we are also in interactive mode, start the interactive session.
  when (Options.interactiveMode opts)
    $ Repl.interactively replOpts e Repl.updateMenu
