{-# OPTIONS_GHC -Wall -Wcompat #-}
-- | Various helper methods for managing external resources.
module Muste.Data (readGrammar) where

import Prelude ()
import Muste.Prelude
import System.FilePath (FilePath, (</>), (<.>))
import qualified System.Directory as Directory
import Data.ByteString (ByteString)
import qualified Data.ByteString as ByteString

-- | Read a grammar file from the file system in a portable fashion.
readGrammar :: String -> IO ByteString
readGrammar = grammar >=> ByteString.readFile

grammarDir :: IO FilePath
grammarDir = (</> "grammars") <$> getDataDir

-- | Get's the data directory for this project.
getDataDir ∷ IO FilePath
getDataDir = Directory.getXdgDirectory Directory.XdgData "muste"

grammar :: FilePath -> IO FilePath
grammar g = do
  d ← grammarDir
  pure $ d </> g <.> "pgf"
