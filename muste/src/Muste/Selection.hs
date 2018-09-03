{-# OPTIONS_GHC -Wall #-}
{-# Language OverloadedStrings, InstanceSigs #-}
-- | A 'Set' with a dfferent 'Ord' instance.
module Muste.Selection (Selection, fromList, toList) where

import Prelude ()
import Muste.Prelude
import qualified Data.Text.Prettyprint.Doc as Doc
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

-- | A selection represents parts of a 'Linearization' w.r.t a
-- linearized 'TTree'.
newtype Selection = Selection { runSelection ∷ IntSet }

deriving instance Show Selection
deriving instance Semigroup Selection
deriving instance Monoid Selection
deriving instance Eq Selection

instance Ord Selection where
  compare (runSelection → xs) (runSelection → ys)
    = case IntSet.size xs `compare` IntSet.size ys of
      EQ → xs `compare` ys
      x  → x

instance Pretty Selection where
  pretty = Doc.pretty . show . IntSet.toList . runSelection

deriving instance ToJSON Selection
deriving instance FromJSON Selection

instance IsList Selection where
  type Item Selection = Int

  -- | Generate a selection from a list of indices.  The incides must
  -- correspond the index into some 'Linearization'.
  fromList ∷ [Int] → Selection
  fromList = Selection . IntSet.fromList

  -- | Convert a selection to a list of indices.
  toList ∷ Selection → [Int]
  toList = IntSet.toList . runSelection
