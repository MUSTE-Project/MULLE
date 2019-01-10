{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language RecordWildCards #-}

module Main (main) where

import Prelude ()
import Muste.Prelude
import qualified Data.Binary                  as Binary
import qualified Data.Text                    as Text

import Muste.Grammar (Grammar)
import qualified Muste.Util                   as Util
import qualified Muste.Menu                   as Menu
import qualified Muste.AdjunctionTrees        as AdjTrees
import qualified Muste.Grammar                as Grammar
import qualified Muste.Linearization          as Linearization
import qualified Muste.Repl                   as Repl
import qualified Options                      as O

makeEnv :: Text -> O.SearchOptions -> O.MusteOptions -> IO Repl.Env
makeEnv grammar searchOpts O.MusteOptions{..} =
    Repl.Env <$> 
    do g <- getGrammar grammar
       case input of
         Nothing -> return $ Util.unsafeGetContext (builderInfo searchOpts) g language
         Just p  -> do adj <- Binary.decodeFile p
                       return $ Linearization.Context g (Util.unsafeGetLang g language) adj

getGrammar :: Text -> IO Grammar
getGrammar = Grammar.getGrammarOneOff

builderInfo :: O.SearchOptions -> AdjTrees.BuilderInfo
builderInfo O.SearchOptions{..} =
    AdjTrees.BuilderInfo { searchDepth = adjTreeSearchDepth
                         , searchSize  = adjTreeSearchSize
                         }

pruneOpts :: O.SearchOptions -> Menu.PruneOpts
pruneOpts O.SearchOptions{..} =
    Menu.PruneOpts { searchDepth = pruneSearchDepth
                   , searchSize  = pruneSearchSize
                   }

muste :: Text -> O.SearchOptions -> O.MusteOptions -> IO ()
muste grammar searchOpts opts@O.MusteOptions{..} =
    do e <- makeEnv grammar searchOpts opts
       if null sentences then
           -- If not sentences are supplied on the command line, start the interactive session.
           Repl.interactively replOpts e (Repl.updateMenu . Text.pack)
       else
           -- If there are any sentences supplied on the command line, run them all.
           Repl.detachedly replOpts e (mapM_ Repl.updateMenu sentences)
    where replOpts :: Repl.Options
          replOpts = Repl.Options printNodes printCompact (pruneOpts searchOpts)

precompute :: Text -> O.SearchOptions -> O.PrecomputeOptions -> IO ()
precompute grammar searchOpts O.PrecomputeOptions{..} = 
    do g <- getGrammar grammar
       Binary.encodeFile output $ AdjTrees.getAdjunctionTrees (builderInfo searchOpts) g

main :: IO ()
main = do O.Options{command=cmd, ..} <- O.getOptions
          case cmd of
            O.Muste      opts -> muste      grammar searchOptions opts
            O.Precompute opts -> precompute grammar searchOptions opts
