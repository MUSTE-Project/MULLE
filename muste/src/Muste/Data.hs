-- | Various helper methods for managing external resources.
module Muste.Data (embedGrammar) where

import System.FilePath (FilePath, (</>), (<.>))
import Data.FileEmbed (embedFile, makeRelativeToProject)
import Language.Haskell.TH (Q, Exp)

-- | Embed the contents of a @.pgf@-file directly into the source
-- code.  The argument to @embedGrammar@ is an identifier for the
-- grammar-file in the form of @GROUP/GRAMMAR@.  For instance
-- @novo_modo/PrimaLat@.  This function handles path resolution.
embedGrammar :: String -> Q Exp
embedGrammar p = do
  f <- makeRelativeToProject $ grammar p
  embedFile f

dataDir :: FilePath
dataDir = "data"

grammarDir :: FilePath
grammarDir = dataDir </> "grammars"

grammar :: FilePath -> FilePath
grammar g = grammarDir </> g <.> "pgf"
