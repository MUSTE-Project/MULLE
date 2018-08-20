{-# Language OverloadedStrings #-}
-- | A 'Set' with a dfferent 'Ord' instance.
module Muste.Selection (Selection, fromList, toList) where

import Prelude hiding (fail)
import Data.Aeson
import Data.Text.Prettyprint.Doc (Pretty(..))
import qualified Data.Text.Prettyprint.Doc as Doc
import Data.List
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

-- | A selection represents parts of a 'Linearization' w.r.t a
-- linearized 'TTree'.
newtype Selection = Selection { runSelection ∷ IntSet }

deriving instance Show Selection
deriving instance Monoid Selection
deriving instance Eq Selection

instance Ord Selection where
  compare (runSelection → xs) (runSelection → ys)
    = case IntSet.size xs `compare` IntSet.size ys of
      EQ → xs `compare` ys
      x  → x

instance Pretty Selection where
  pretty = Doc.pretty . intercalate ","
    . map show . IntSet.toList . runSelection

deriving instance ToJSON Selection
deriving instance FromJSON Selection

fromList ∷ [Int] → Selection
fromList = Selection . IntSet.fromList

toList ∷ Selection → [Int]
toList = IntSet.toList . runSelection
