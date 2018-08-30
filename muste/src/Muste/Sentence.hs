{-# OPTIONS_GHC -Wall #-}
{-# Language RecordWildCards #-}
-- | An interface for (un-)annotated sentences.  For the two
-- respective implementations see:
--
--   * "Muste.Sentence.Annotated"
--   * "Muste.Sentence.Unannotated"
module Muste.Sentence
  ( Sentence.Sentence(..)
  , Sentence.Linearization
  , Sentence.Language(..)
  , Sentence.stringRep
  , Token.IsToken
  , disambiguate
  , Sentence.Grammar(..)
  -- Why can't I just do this:
  -- , module Sentence
  ) where

import Data.Function ((&))

import Muste.Linearization.Internal (Context)
import Muste.Tree.Internal (TTree)
import qualified Muste.Linearization.Internal as OldLinearization
import qualified Muste.Grammar.Internal as Grammar

import qualified Muste.Sentence.Class    as Sentence
import qualified Muste.Sentence.Token    as Token

parse ∷ Context → String → [TTree]
parse (OldLinearization.Context { .. })
  = Grammar.parseSentence ctxtGrammar ctxtLang

-- | Get all 'TTree's correspnding to this sentence in a given
-- context.  It's an invariant that the sentence is a valid sentence
-- in the grammar /and/ language given by the 'Context'.
disambiguate
  ∷ Sentence.Sentence s
  ⇒ Token.IsToken (Sentence.Token s)
  ⇒ Context
  → s
  → [TTree]
disambiguate c s
  = Sentence.linearization s
  & Sentence.stringRep
  & parse c
