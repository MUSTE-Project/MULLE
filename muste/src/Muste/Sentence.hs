{-# OPTIONS_GHC -Wall #-}
{-# Language
 DeriveGeneric,
 GeneralizedNewtypeDeriving,
 NamedFieldPuns,
 OverloadedStrings
#-}

module Muste.Sentence
  ( buildContexts
  , languages
  , getLangAndContext
  , Context(Context, ctxtGrammar, ctxtLang, ctxtPrecomputed)
  , textRep
  , disambiguate
  , Language(Language)
  , Linearization(Linearization)
  , Annotated(linearization, language)
  , mkLinearization
  , mergeL
  , annotate
  , fromText
  , Token(Token, concrete, classes)
  , linTree
  , linearizeTree
  ) where

import Muste.Util (toBlob, fromBlob)
import Database.SQLite.Simple.ToField (ToField(..))
import Database.SQLite.Simple.FromField (FromField(..))

import Control.Monad.Catch (MonadThrow(throwM), Exception)
import Data.Function ((&), on)
import GHC.Generics (Generic)

import Data.Aeson (ToJSON(..), FromJSON(..), (.=), (.:))
import qualified Data.Aeson as Aeson
import Data.Binary (Binary)
import qualified Data.Text as Text
import Data.Text (Text)
import Data.Text.Prettyprint.Doc (Pretty(..))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

import qualified PGF

import Muste.Tree (TTree, Path, Category)
import qualified Muste.Tree as Tree
import qualified Muste.Grammar as Grammar
import Muste.AdjunctionTrees (BuilderInfo, AdjunctionTrees, getAdjunctionTrees)

parse :: Context -> Text -> [TTree]
parse (Context ctxtGrammar ctxtLang _ctxtPrecomputed)
  = Grammar.parseSentence ctxtGrammar ctxtLang

-- | Get all 'TTree's correspnding to this sentence in a given
-- context.  It's an invariant that the sentence is a valid sentence
-- in the grammar /and/ language given by the 'Context'.
disambiguate :: Context -> Annotated -> [TTree]
disambiguate c s
  = linearization s
  & textRep
  & parse c


--------------------------------------------------------------------------------

-- | Given a grammar creates a mapping from all the languages in that
-- grammar to their respective 'Context's.
buildContexts :: BuilderInfo -> Grammar.Grammar -> Map Text Context
buildContexts nfo g = buildContext nfo g <$> languages g

-- | Memoize all @AjdunctionTrees@ for a given grammar and language.
buildContext :: BuilderInfo -> Grammar.Grammar -> PGF.Language -> Context
buildContext nfo g lang =
  Context g lang (getAdjunctionTrees nfo g)

-- | Gets all the languages in the grammar.
languages :: Grammar.Grammar -> Map Text PGF.Language
languages g
  = Map.fromList $ mkCtxt <$> PGF.languages (Grammar.pgf g)
  where
  mkCtxt :: PGF.Language -> (Text, PGF.Language)
  mkCtxt lang = (Text.pack $ PGF.showCId lang, lang)

-- | Given an identifier for a grammar, looks up that grammar and then
-- creates a mapping from all the languages in that grammar to their
-- respective 'Context's.
--
-- This method will throw a 'FileNotFoundException' if the grammar
-- cannot be located.
getLangAndContext :: Grammar.MonadGrammar m => BuilderInfo -> Text -> m (Map Text Context)
getLangAndContext nfo idf = do
  g <- Grammar.getGrammar idf
  pure $ buildContexts nfo g

-- | Remember all 'AdjunctionTrees' in a certain 'PGF.Language' for a
-- certain 'Grammar'.
data Context = Context
  { ctxtGrammar :: Grammar.Grammar
  , ctxtLang   :: PGF.Language
  , ctxtPrecomputed :: AdjunctionTrees
  }


--------------------------------------------------------------------------------

data Annotated = Annotated
  { language      :: Language
  , linearization :: Linearization
  }
  deriving (Show, Generic)

instance ToJSON Annotated where
  toJSON (Annotated language linearization) = Aeson.object
    [ "language"      .= language
    , "linearization" .= linearization
    ]

instance FromJSON Annotated where
  parseJSON = Aeson.withObject "word"
    $ \o -> Annotated
    <$> o .: "language"
    <*> o .: "linearization"

instance Binary Annotated where

instance ToField Annotated where
  toField = toBlob

instance FromField Annotated where
  fromField = fromBlob


annotate :: MonadThrow m => Exception e => e -> Context -> Annotated -> m Annotated
annotate err ctxt sent
  = linearization sent
  & textRep
  & Grammar.parseSentence (ctxtGrammar ctxt) (ctxtLang ctxt)
  & map unambigSimpl
  & merge err
  where
    unambigSimpl :: TTree -> Annotated
    unambigSimpl tree = annotated ctxt (language sent) tree


fromText :: Text -> Text -> Text -> Annotated
fromText g l xs
  = Annotated (Language g l) (Linearization [Token s mempty | s <- Text.words xs])


-- | @'mkLinearization' ctxt tree@ creates a 'Linearization' of @tree@.
-- The 'Linearization' will be a valid such in the grammar and languages
-- specified by the 'Context' @ctxt@.
mkLinearization :: Context -> TTree -> Linearization 
mkLinearization ctxt tree = Linearization [ step tok | tok <- linearizeTree ctxt tree ]
  where
    step :: (Text, Path) -> Token
    step (ltlin, ltpath) = mkToken ltlin (names ltpath)
    -- Throws if the path is not found /and/ only finds a single function name!
    names :: Tree.Path -> [Text]
    names path = case Tree.selectNode tree path of
                   Nothing -> error "Expected to find path here"
                   Just node -> [Tree.unCategory (name node)]
    name :: TTree -> Category
    name (Tree.TNode n _ _) = n
    name (Tree.TMeta _)     = error "Expected saturated tree"


linTree :: Context -> TTree -> ([Text], [Category])
linTree ctxt tree = (toks, nods)
  where
    toks = [ ltlin | (ltlin, _) <- lintokens ]
    nods = [ Tree.lookupNode tree ltpath | (_, ltpath) <- lintokens ]
    lintokens = linearizeTree ctxt tree


linearizeTree :: Context -> TTree -> [(Text, Path)]
linearizeTree (Context grammar language _) ttree =
  if not (Grammar.isEmptyGrammar grammar)
     && language `elem` PGF.languages (Grammar.pgf grammar)
     && not (null brackets)
  then Grammar.bracketsToTuples ttree $ head brackets
  else [("?0", [])]
  where
    brackets = Grammar.brackets grammar language ttree


-- | @'annotated' c t@ creates a 'Sentence' of @t@.  The 'Sentence' 
-- will be a valid such in the grammar and languages specified by the
-- 'Context' @c@.
--
-- See also the documentation for 'linearization'.
annotated :: Context -> Language -> TTree -> Annotated
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

mergeL :: Linearization -> Linearization -> Linearization
mergeL (Linearization a) (Linearization b)
  = Linearization (zipWith mergeToken a b)


--------------------------------------------------------------------------------

data Language = Language { grammar :: Text, lang :: Text }
  deriving (Eq, Ord, Show, Generic)

instance ToJSON Language where
  toJSON (Language grammar lang) = Aeson.object
    [ "grammar"  .= grammar
    , "language" .= lang
    ]

instance FromJSON Language where
  parseJSON = Aeson.withObject "word"
    $ \o -> Language
    <$> o .: "grammar"
    <*> o .: "language"

instance Binary Language where


--------------------------------------------------------------------------------

newtype Linearization = Linearization [Token]
  deriving (Eq, Ord, Show, FromJSON, ToJSON, Binary, Generic)

instance ToField Linearization where
  toField = toBlob

instance FromField Linearization where
  fromField = fromBlob

instance Pretty Linearization where
  pretty = pretty . textRep

textRep :: Linearization -> Text
textRep (Linearization as) = Text.unwords (map concrete as)


--------------------------------------------------------------------------------

data Token = Token
  { concrete :: Text
  , classes  :: Set Text
  }
  deriving (Eq, Ord, Show, Generic)

instance Binary Token where

instance ToField Token where
  toField = toBlob

instance FromField Token where
  fromField = fromBlob

instance ToJSON Token where
  toJSON (Token concrete classes) = Aeson.object
    [ "concrete" .= concrete
    , "classes"  .= classes
    ]

instance FromJSON Token where
  parseJSON = Aeson.withObject "token"
    $ \o -> Token
    <$> o .: "concrete"
    <*> o .: "classes"

instance Pretty Token where
  pretty (Token s _) = pretty s

mkToken :: Text -> [Text] -> Token
mkToken c a = Token c (Set.fromList a)

mergeToken :: Token -> Token -> Token
mergeToken (Token a0 a1) (Token _ b1) = Token
  { concrete = a0
  , classes  = Set.union a1 b1
  }
