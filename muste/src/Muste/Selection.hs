{-# Language OverloadedStrings #-}
-- | A 'Set' with a dfferent 'Ord' instance.
module Muste.Selection (Selection, fromList) where

import Prelude hiding (fail)
import Data.Aeson
import qualified Data.Aeson.Encoding as Aeson
import Data.Text.Prettyprint.Doc (Pretty(..), Doc)
import qualified Data.Text.Prettyprint.Doc as Doc
import Data.List
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.String.Conversions (convertString)
import Control.Monad.Fail (MonadFail(fail))
import Data.Text (Text)
import Text.Read (readEither)

import Muste.Tree (Path)
import Muste.Common

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

fromText ∷ MonadFail m ⇒ Text → m Selection
fromText t = case readEither $ convertString t of
  Right x → pure $ fromList x
  Left err → fail err

deriving instance ToJSON Selection
deriving instance FromJSON Selection

shownToJSONKey ∷ (a → String) → ToJSONKeyFunction a
shownToJSONKey show' = ToJSONKeyText f g
  where f = convertString @String . show'
        g = Aeson.text . convertString . show'

showableToJSONKey ∷ Show a ⇒ ToJSONKeyFunction a
showableToJSONKey = shownToJSONKey show

fromList ∷ [Int] → Selection
fromList = Selection . IntSet.fromList

toList ∷ Selection → [Int]
toList = IntSet.toList . runSelection
