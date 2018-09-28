{-# OPTIONS_GHC -Wall #-}
{-# Language RecordWildCards, NamedFieldPuns, TemplateHaskell,
  DeriveAnyClass, OverloadedStrings, MultiParamTypeClasses,
  DerivingStrategies #-}
module Main (main) where

import Muste.Prelude
import qualified Data.Binary as Binary

import Muste (Grammar)
import qualified Muste.Util             as Muste
import Muste.AdjunctionTrees (BuilderInfo(..))
import qualified Muste.Menu as Menu
import qualified Muste.AdjunctionTrees as AdjunctionTrees
import Muste.AdjunctionTrees (AdjunctionTrees)
import qualified Muste.Grammar.Internal as Grammar
import Muste.Linearization.Internal (Context(Context))
import qualified Data.Text as Text

import Options (Options(Options), PreComputeOpts(PreComputeOpts))
import qualified Options
import qualified Muste.Repl             as Repl

makeEnv ∷ Options → IO Repl.Env
makeEnv opts@(Options{..}) = Repl.Env <$> getContext
  where
  g = unsafeLookupGrammar grammar
  getContext ∷ IO Context
  getContext = case input of
    Nothing → pure  $ Muste.unsafeGetContext (builderInfo opts) g language
    Just p → do
      adj ← Binary.decodeFile @AdjunctionTrees p
      pure $ Context g (Muste.unsafeGetLang g language) adj

unsafeLookupGrammar ∷ Text → Grammar
unsafeLookupGrammar g
  = fromMaybe (error "Grammar not found") $ Grammar.lookupGrammar g

builderInfo ∷ Options → BuilderInfo
builderInfo Options { searchOptions = Options.SearchOptions{..} }
  = BuilderInfo
  { searchDepth = adjTreeSearchDepth
  , searchSize  = adjTreeSearchSize
  }

muste ∷ Options.Options → IO ()
muste opts@Options{ searchOptions = Options.SearchOptions{..}, ..} = do
  let pruneOpts ∷ Menu.PruneOpts
      pruneOpts = Menu.PruneOpts
        { searchDepth = pruneSearchDepth
        , searchSize  = pruneSearchSize
        }
      replOpts ∷ Repl.Options
      replOpts = Repl.Options printNodes printCompact pruneOpts
  e ← makeEnv opts
  -- If there are any sentences supplied on the command line, run them
  -- all.
  void $ Repl.detachedly replOpts e (traverse Repl.updateMenu sentences)
  -- If we are also in interactive mode, start the interactive session.
  when interactiveMode
    $ Repl.interactively replOpts e (Repl.updateMenu . Text.pack)

precompute ∷ Options.PreComputeOpts → IO ()
precompute Options.PreComputeOpts{ searchOptions = Options.SearchOptions{..}, ..}
  = Binary.encodeFile output $ AdjunctionTrees.getAdjunctionTrees opts g
  where
  g = unsafeLookupGrammar grammar
  opts ∷ BuilderInfo
  opts = BuilderInfo
    { searchDepth = adjTreeSearchDepth
    , searchSize  = adjTreeSearchSize
    }

main :: IO ()
main = do
  Options.Command cmd ← Options.getOptions
  case cmd of
    Options.Muste opts → muste opts
    Options.PreCompute g → precompute g
