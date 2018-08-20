module Muste.Grammar.TH (tree) where

import Control.Monad.Fail (MonadFail)
import Language.Haskell.TH (Q, Exp)
import Language.Haskell.TH.Syntax (lift)
import qualified Muste.Grammar.Internal as Grammar (lookupGrammarM, parseTTree)
import Text.Printf

import Muste.Tree (TTree)

-- | Generate a tree from an identifier for a language and the GF
-- representation of that tree.
tree
  ∷ String -- ^ An identifier for the language
  → String -- ^ The tree
  → Q Exp
tree idf s = parseTree idf s >>= lift

parseTree ∷ MonadFail m ⇒ String → String → m TTree
parseTree idf s = do
  g ← Grammar.lookupGrammarM (err idf) idf
  pure $ Grammar.parseTTree g s
  where
  err = printf "Muste.Grammar.TH.tree: Unknown grammar %s"
