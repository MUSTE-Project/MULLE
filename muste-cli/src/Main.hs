{-# OPTIONS_GHC -Wall -Wcompat #-}

module Main (main) where

import qualified Data.Binary as Binary

import qualified Muste   as M
import qualified Repl    as R
import qualified Options as O


runMuste :: M.MUState -> O.MusteOptions -> IO ()
runMuste mustate opts
    | null sentences = R.interactively replEnv
    | otherwise      = R.detachedly    replEnv sentences
 where 
    replEnv   = R.Env (O.printOptions opts) (O.pruneOptions opts) mustate (O.language opts)
    sentences = O.sentences opts


runPrecompute :: M.MUState -> O.PrecomputeOptions -> IO ()
runPrecompute mustate precompOpts =
    Binary.encodeFile (O.output precompOpts) adjTrees
  where
    (_g, adjTrees) = M.lookupLessonMU mustate R.grName


main :: IO ()
main = do opts <- O.getOptions
          mustate <- M.loadGrammarMU "" M.emptyMUState (R.grName, O.grammar opts, O.builderInfo opts)
          case O.command opts of
            O.Muste      mopts -> runMuste      mustate mopts 
            O.Precompute popts -> runPrecompute mustate popts
