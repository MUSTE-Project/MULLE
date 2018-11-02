module Test.Common (failDoc, renderDoc) where

import Prelude
import Muste.Prelude
import Muste.Prelude.Extra

import Muste.Grammar (Grammar)
import qualified Muste.Grammar.Internal as Grammar
import Data.ByteString (ByteString)
import qualified Data.ByteString.Lazy as LB
import Data.Text.Prettyprint.Doc (Doc, Pretty, layoutCompact)
import Data.Text.Prettyprint.Doc.Render.String (renderString)
import Control.Monad.Fail (MonadFail(fail))
import Test.Tasty.HUnit (Assertion, assertFailure)

import Muste (TTree)

failDoc ∷ Doc a → Assertion
failDoc = assertFailure . renderDoc
