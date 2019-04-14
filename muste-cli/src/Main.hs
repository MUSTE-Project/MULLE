{-# OPTIONS_GHC -Wall -Wcompat #-}
{-# Language
 RecordWildCards
#-}

module Main (main) where

import qualified Data.Binary as Binary
import qualified Data.Text as Text
import Data.Text (Text)

import Muste.Util (lookupFail)
import qualified Muste.Menu as Menu
import qualified Muste.AdjunctionTrees as AdjTrees
import qualified Muste.Grammar as Grammar
import qualified Muste.Linearization as Linearization
import qualified Muste.Repl as Repl
import qualified Options as O


makeEnv :: Text -> O.SearchOptions -> O.MusteOptions -> IO Repl.Env
makeEnv grammar searchOpts O.MusteOptions{..} =
    Repl.Env <$>
    do g <- Grammar.getGrammarOneOff grammar
       case input of
         Nothing -> do let cxts = Linearization.buildContexts (builderInfo searchOpts) g
                       lookupFail err language cxts
         Just p  -> do adj <- Binary.decodeFile p
                       lng <- lookupFail err language $ Linearization.languages g
                       return $ Linearization.Context g lng adj
  where err = "Cannot find language: " ++ Text.unpack language

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
    do g <- Grammar.getGrammarOneOff grammar
       Binary.encodeFile output $ AdjTrees.getAdjunctionTrees (builderInfo searchOpts) g

main :: IO ()
main = do O.Options{command=cmd, ..} <- O.getOptions
          case cmd of
            O.Muste      opts -> muste      grammar searchOptions opts
            O.Precompute opts -> precompute grammar searchOptions opts