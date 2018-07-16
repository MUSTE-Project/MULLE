{-# LANGUAGE OverloadedStrings #-}
module Muste.Linearization.Internal
  ( Context(ctxtGrammar, ctxtPrecomputed)
  , buildContext
  , LinToken(LinToken)
  , Linearization
  , mkLinearization
  , linearizeTree
  ) where

import Data.Aeson
-- This might be the only place we should know of PGF
import qualified PGF
import qualified PGF.Internal as PGF hiding (funs, cats)
import Data.List

import Muste.Tree
import Muste.Grammar
import Muste.Grammar.Internal (ttreeToGFAbsTree)
import Muste.Prune

data LinToken = LinToken
  { _ltpath :: Path
  , _ltlin :: String
  , _ltmatched :: Path
  } deriving (Show)

-- | Remember all 'AdjunctionTrees' in a certain 'PGF.Language' for a
-- certain 'Grammar'.
data Context = Context
  { ctxtGrammar :: Grammar
  , _ctxtLang   :: PGF.Language
  , ctxtPrecomputed :: AdjunctionTrees
  }

-- | A linearization of a tree is the way a @TTree@ is represented in
-- a given language.  It represents the way the sentence is read.
data Linearization = Linearization
  { _lpath :: Path
  , _llin :: String
  } deriving (Show,Eq)

-- FIXME Is this right? I copied this from
-- @Muste.getPrunedSuggestions@ So that I could make 'Linearization'
-- abstract.
-- | Convert a 'LinToken' to a 'Linearization'.
mkLinearization :: LinToken -> Linearization
mkLinearization (LinToken p l _) = Linearization p l

instance FromJSON Linearization where
  parseJSON = withObject "Linearization" $ \v -> Linearization
    <$> v .: "path"
    <*> v .: "lin"

instance ToJSON Linearization where
  toJSON (Linearization path lin) = object
    [ "path" .= path
    , "lin" .= lin
    ]

instance FromJSON LinToken where
  parseJSON = withObject "LinToken" $ \v -> LinToken
    <$> v .: "path"
    <*> v .: "lin"
    <*> v .: "matched"

instance ToJSON LinToken where
  toJSON (LinToken path lin matched) = object
    [ "path"    .= path
    , "lin"     .= lin
    , "matched" .= matched
    ]

-- | Memoize all @AjdunctionTrees@ for a given grammar and language.
buildContext :: Grammar -> PGF.Language -> Context
buildContext grammar lang =
  Context grammar lang (getAdjunctionTrees grammar)

-- lin is the full linearization
-- Maybe fits better in the grammar.
-- | The 'linearizeTree' function linearizes a @TTree@ to a list of
-- tokens and paths to the nodes that create it
linearizeTree :: Context -> TTree ->  [LinToken]
linearizeTree (Context grammar language _) ttree =
  let
    -- Convert the PGF.BracketedString to the list of string/path tuples
    bracketsToTuples :: TTree -> PGF.BracketedString -> [LinToken]
    bracketsToTuples tree bs =
      let
        deep :: TTree -> PGF.BracketedString -> [LinToken]
        deep _     (PGF.Bracket _ _   _ _ _ []) = []
        -- Ordinary leaf
        deep ltree (PGF.Bracket _ fid _ _ _ [PGF.Leaf token]) =
          [LinToken (getPath ltree fid) token []]
        -- Meta leaf
        deep ltree (PGF.Bracket _ fid _ _ [PGF.EMeta id] _) =
          [LinToken (getPath ltree fid) ("?" ++ show id) []]
        -- In the middle of the tree
        deep ltree (PGF.Bracket _ fid _ _ _ bs) =
          broad ltree fid bs []
        deep _ _ = error "Muste.linearizeTree: Non-exhaustive pattern match"
        broad :: TTree -> Int -> [PGF.BracketedString] -> [LinToken] -> [LinToken]
        -- End of node siblings
        broad _     _   []                 ts = ts
        -- Syncategorial word
        broad ltree fid (PGF.Leaf token:bss) ts =
          let
            b = broad ltree fid bss ts
          in
            LinToken (getPath ltree fid) token [] : b
        -- In the middle of the nodes
        broad ltree fid (bs:bss)           ts =
          let
            d = deep ltree bs
            b = broad ltree fid bss ts
          in
            d ++ b
      in
        deep tree bs
    ltree = ttree
    abstree = ttreeToGFAbsTree ttree
    pgfGrammar = pgf grammar
    brackets = PGF.bracketedLinearize pgfGrammar language abstree :: [PGF.BracketedString]
  in
    if not (isEmptyGrammar grammar)
      && language `elem` PGF.languages (pgf grammar)
      && not (null brackets)
    then bracketsToTuples ltree $ head brackets
    else [LinToken [] "?0" []]

