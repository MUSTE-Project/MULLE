{-# LANGUAGE OverloadedStrings #-}
module Muste.Linearization
  ( Context
  , buildContext
  , LinToken(LinToken)
  , Linearization(Linearization)
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

type Context = (Grammar, PGF.Language, AdjunctionTrees)

data Linearization = Linearization
  { _lpath :: Path
  , _llin :: String
  } deriving (Show,Eq)

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

buildContext :: Grammar -> PGF.Language -> Context
buildContext grammar lang = (grammar, lang, getAdjunctionTrees grammar)

-- lin is the full linearization
-- Maybe fits better in the grammar.
-- | The 'linearizeTree' function linearizes a TTree to a list of tokens and pathes to the nodes that create it
linearizeTree :: Context -> TTree ->  [LinToken]
linearizeTree (grammar, language, _) ttree = 
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

