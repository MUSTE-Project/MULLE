{-# OPTIONS_GHC -Wall #-}
{-# Language
 DeriveAnyClass,
 DeriveGeneric,
 DerivingStrategies,
 FlexibleContexts,
 FlexibleInstances,
 GeneralizedNewtypeDeriving,
 NamedFieldPuns,
 OverloadedStrings,
 RecordWildCards,
 ScopedTypeVariables,
 StandaloneDeriving,
 TypeApplications,
 TypeFamilies
#-}

module Muste.Sentence
  ( stringRep
  , disambiguate
  , Language(Language)
  , Grammar(Grammar)
  , Linearization
  , Annotated(linearization, language)
  , mkLinearization
  , mergeL
  , annotate
  , fromText
  , Token(Token, concrete, classes)
  ) where

import Muste.Util (toBlob, fromBlob)
import Database.SQLite.Simple.ToField (ToField(..))
import Database.SQLite.Simple.FromField (FromField(..))

import Control.Monad.Catch (MonadThrow(throwM), Exception)
import Control.Category ((>>>))
import Control.DeepSeq (NFData)
import Data.Typeable (Typeable)
import Data.Function ((&), on)
import GHC.Generics (Generic)

import Data.Aeson (ToJSON(..), FromJSON(..), (.=), (.:))
import qualified Data.Aeson as Aeson
import Data.Binary (Binary, get, put)
import Data.MonoTraversable (otoList)
import qualified Data.Text as Text
import Data.Text (Text)
import Data.Maybe (fromMaybe)
import qualified Data.Vector as Vector
import GHC.Exts (IsList(fromList, toList, Item))
import Data.String (IsString(fromString))
import Data.Text.Prettyprint.Doc (Pretty(..))
import Data.Vector (Vector)
import Data.Set (Set)
import qualified Data.Set as Set

import Muste.Tree (TTree, Category)
import qualified Muste.Tree as Tree
import qualified Muste.Linearization as OldLin
import qualified Muste.Grammar as Grammar

parse :: OldLin.Context -> Text -> [TTree]
parse OldLin.Context{..}
  = Grammar.parseSentence ctxtGrammar ctxtLang

-- | Get all 'TTree's correspnding to this sentence in a given
-- context.  It's an invariant that the sentence is a valid sentence
-- in the grammar /and/ language given by the 'Context'.
disambiguate :: OldLin.Context -> Annotated -> [TTree]
disambiguate c s
  = linearization s
  & stringRep
  & parse c


--------------------------------------------------------------------------------

data Annotated = Annotated
  { language      :: Language
  , linearization :: Linearization Token
  }

deriving instance Show Annotated

instance ToJSON Annotated where
  toJSON (Annotated {..}) = Aeson.object
    [ "language"      .= language
    , "linearization" .= linearization
    ]

instance FromJSON Annotated where
  parseJSON = Aeson.withObject "word"
    $ \o -> Annotated
    <$> o .: "language"
    <*> o .: "linearization"

deriving instance Generic Annotated
instance Binary Annotated where

instance ToField Annotated where
  toField = toBlob

instance FromField Annotated where
  fromField = fromBlob


annotate :: MonadThrow m => Exception e => e -> OldLin.Context -> Annotated -> m Annotated
annotate e c@OldLin.Context{..} s
  = linearization s
  & stringRep
  & Grammar.parseSentence ctxtGrammar ctxtLang
  & map unambigSimpl
  & merge e
  where
  unambigSimpl :: TTree -> Annotated
  unambigSimpl t
    = annotated c l t
  l :: Language
  l = language s


fromText :: Text -> Text -> Text -> Annotated
fromText g l xs
  = Annotated (Language (Grammar g) l) (fromList (go <$> Text.words xs))
  where
  go :: Text -> Token
  go s = Token s mempty


-- | @'mkLinearization' c t@ creates a 'Linearization' of @t@. The
-- 'Linearization' will be a valid such in the grammar and languages
-- specified by the 'Context' @c@.
--
-- This implementation reuses the functionality from
-- 'Muste.OldLin.Internal.mkLin' and then converts it to the
-- new representation.  In doing so note in particular that we do not
-- create ambiguities in the individual words.  Eachs 'Token' will
-- correspond exactly to an internal node in the 'TTree' (idenfitied
-- by the "name" of that node).
mkLinearization :: OldLin.Context -> TTree -> Linearization Token
mkLinearization c t
  -- Reuse functionality from 'Muste.OldLin.Internal'
  = OldLin.linearizeTree c t
  & otoList
  -- Convert old representation to new.
  & fmap step
  & fromList
  where
  step :: OldLin.LinToken -> Token
  step (OldLin.LinToken { .. })
    = mkToken ltlin (fromList @[Text] $ names ltpath)
  -- Throws if the path is not found /and/ only finds a single
  -- function name!
  names :: Tree.Path -> [Text]
  names
    =   Tree.selectNode t
    >>> fromMaybe (error "Expected to find path here")
    >>> name
    >>> Tree.unCategory
    >>> pure @[]
  name :: TTree -> Category
  name (Tree.TNode n _ _) = n
  name (Tree.TMeta _)     = error "Expected saturated tree"

-- | @'annotated' c t@ creates a 'Sentence' of @t@.  The 'Sentence' 
-- will be a valid such in the grammar and languages specified by the
-- 'Context' @c@.
--
-- See also the documentation for 'linearization'.
annotated :: OldLin.Context -> Language -> TTree -> Annotated
annotated c l t = Annotated l $ mkLinearization c t

-- | Merge multiple
merge :: MonadThrow m => Exception e => e -> [Annotated] -> m Annotated
merge e [] = throwM e
merge _ xs = pure $ foldl1 merge1 xs

-- Merge two sentences, assuming they have the same language.
merge1 :: Annotated -> Annotated -> Annotated
merge1 a b = Annotated lang ((mergeL `on` linearization) a b)
  where
  lang = language a

mergeL
  :: Linearization Token
  -> Linearization Token
  -> Linearization Token
mergeL (Linearization a) (Linearization b)
  = Linearization (Vector.zipWith mergeToken a b)


--------------------------------------------------------------------------------

newtype Grammar = Grammar Text

deriving stock   instance Show      Grammar
deriving newtype instance Eq        Grammar
deriving newtype instance Ord       Grammar
deriving newtype instance FromJSON  Grammar
deriving newtype instance ToJSON    Grammar
deriving stock   instance Generic   Grammar
deriving newtype instance Binary    Grammar
deriving newtype instance FromField Grammar
deriving newtype instance ToField   Grammar
deriving newtype instance IsString  Grammar

data Language = Language
  -- NB This field is not in use.
  { grammar  :: Grammar
  , lang     :: Text
  }
                             
deriving stock instance Show Language
deriving stock instance Eq   Language
deriving stock instance Ord  Language

-- | The implementation is a bit hacky, we just use the read instance
-- for pairs to be able to parse a 'Language'.  So the language must
-- be given as:
--
--   "(\"grammar\", \"lang\")"
--
-- Note the gratiutious double-quotes.  Not exactly the most
-- elegant...
instance IsString Language where
  fromString s = Language (fromString g) (fromString l)
    where
    (g, l) = read @(String, String) s

instance ToJSON Language where
  toJSON (Language {..}) = Aeson.object
    [ "grammar"  .= grammar
    , "language" .= lang
    ]

instance FromJSON Language where
  parseJSON = Aeson.withObject "word"
    $ \o -> Language
    <$> o .: "grammar"
    <*> o .: "language"

deriving stock    instance Generic Language
deriving anyclass instance Binary  Language


--------------------------------------------------------------------------------

newtype Linearization a = Linearization
  { unLinearization :: Vector a }

deriving instance Show a => Show (Linearization a)
deriving newtype instance FromJSON a => FromJSON (Linearization a)
deriving newtype instance ToJSON a => ToJSON (Linearization a)
deriving instance Eq a => Eq (Linearization a)
deriving instance Ord a => Ord (Linearization a)
deriving instance Generic a => Generic (Linearization a)
instance (Generic a, NFData a) => NFData (Linearization a) where

-- There is no 'Binary' instance for 'Vector', so we go via '[]'.
instance Binary a => Binary (Linearization a) where
  put = put @[a] . Vector.toList . unLinearization
  get = Linearization . Vector.fromList <$> get @[a]

instance (Binary a, Typeable a) => ToField (Linearization a) where
  toField = toBlob

instance (Binary a, Typeable a) => FromField (Linearization a) where
  fromField = fromBlob

instance IsList (Linearization a) where
  type Item (Linearization a) = a
  fromList = Vector.fromList >>> Linearization
  toList = unLinearization >>> Vector.toList

instance Pretty (Linearization Token) where
  pretty = pretty . stringRep

-- FIXME change name to @textRep@
stringRep :: Linearization Token -> Text
stringRep
  =   toList
  >>> fmap concrete
  >>> Text.unwords


--------------------------------------------------------------------------------

data Token = Token
  { concrete :: Text
  , classes  :: Set Text
  }

deriving instance Show Token
deriving instance Generic Token
deriving instance Eq Token
deriving instance Ord Token
instance Binary Token where
instance ToField Token where
  toField = toBlob
instance FromField Token where
  fromField = fromBlob
instance ToJSON Token where
  toJSON Token{..} = Aeson.object
    [ "concrete" .= concrete
    , "classes"  .= classes
    ]
instance FromJSON Token where
  parseJSON = Aeson.withObject "token"
    $ \o -> Token
    <$> o .: "concrete"
    <*> o .: "classes"
instance NFData Token where

instance Pretty Token where
  pretty (Token s _) = pretty s

mkToken :: Text -> [Text] -> Token
mkToken c a = Token c (Set.fromList a)

mergeToken :: Token -> Token -> Token
mergeToken (Token a0 a1) (Token _ b1) = Token
  { concrete = a0
  , classes  = Set.union a1 b1
  }
