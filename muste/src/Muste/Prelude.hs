{-# OPTIONS_GHC -Wall #-}
module Muste.Prelude
  ( module X
  , identity
  , module Extraneous
  , module Unsafe
  ) where

import Prelude as X
  -- Classes
  (Ord(..), Show(show), Monoid(..), Eq(..), Ordering(..),
  Read, Foldable, Functor(..), Applicative(..), Monad((>>=)),
  Enum(..), Num(..),

  -- Data
  IO, Int, Integer, Maybe(..), Either(..), Bool(..), Char,
  -- Aliases
  String, FilePath,

  (.), ($), ($!), either, pure, (||), (&&), length, otherwise,
  splitAt, (<$>), fromInteger, uncurry, curry, not, null, filter,
  zipWith, zip, fst, snd, all, any, reverse, maximum, minimum, max,
  min, sum, unwords, words, lines, unlines, or, and, notElem, elem,
  (<*>), foldMap, putStrLn, putStr, flip, const, sequence, take,
  mapM_, mapM, ioError, error, repeat, foldl, seq, mod)
import Data.List                 as X (sort)
import Data.Bool                 as X (bool)
import Data.Function             as X ((&), on)
import Data.Traversable          as X (Traversable(..))
import Control.Monad             as X ((>=>), void, when, guard)
import Control.Monad.IO.Class    as X (MonadIO(liftIO))
import Control.Exception         as X
  (Exception, SomeException, throwIO, displayException, throw)
import Data.Maybe                as X (fromMaybe, fromJust, listToMaybe)
import Control.Monad.Fail        as X (MonadFail(fail))
import Control.Monad.Catch       as X (MonadThrow(throwM))
import Data.Text                 as X (Text)
import Control.Category          as X ((>>>), (<<<))
import Text.Printf               as X (printf)
import Data.Text.Prettyprint.Doc as X (Doc, Pretty(pretty))
import Data.Aeson                as X (FromJSON, ToJSON)
import Data.Semigroup            as X (Semigroup(..))
import Text.Read                 as X (readEither, readMaybe)
import GHC.Generics              as X (Generic)
import Data.Binary               as X (Binary)
import GHC.Exts                  as X (IsList(fromList, toList, Item))
import Data.String               as X (IsString)
import Control.Applicative       as X (Alternative(..))

import Prelude as Extraneous
  -- Use 'pure'
  ( return
  -- Use '(>>=)'
  , concatMap
  -- Use 'fmap'
  , map
  -- Use '(<>)'
  , (++)
  )

-- We could maybe emit a warning when using these?
import Prelude as Unsafe
  -- Use pattern-matching or perhaps 'listToMaybe'.
  ( head
  -- Use 'readMaybe', 'readEither' os similiar.
  , read
  -- You probably want a vector/array.
  , (!!)
  -- Use 'error'
  , undefined
  , foldl1
  )

identity ∷ a → a
identity a = a
