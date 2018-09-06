{-# OPTIONS_GHC -Wall #-}
module Muste.Grammar.Embed (grammar) where

import Language.Haskell.TH (Q, Exp(TupE, LitE), Lit(StringL))
import qualified Muste.Data as Data

-- | Embed a @(String, ByteString)@ into your program.  The string is
-- an identifier for a specific grammar, a grammar with that identier
-- must exist in the database.  That identifier along with the
-- contents of that file is returned.
grammar :: String -> Q Exp
grammar s = go <$> Data.embedGrammar s
  where
  go :: Exp -> Exp
  go fileContents = TupE [LitE (StringL s), fileContents ]
