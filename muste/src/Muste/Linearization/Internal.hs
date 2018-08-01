{-# Language OverloadedStrings, GeneralizedNewtypeDeriving #-}
module Muste.Linearization.Internal
  ( Context(ctxtGrammar, ctxtPrecomputed)
  , buildContext
  , Linearization
  , OldLinearization
  , linearizeTree
  , langAndContext
  , mkLin
  ) where

import Data.Aeson
-- This might be the only place we should know of PGF
import qualified PGF
import qualified PGF.Internal as PGF hiding (funs, cats)
import Data.Function (on)

import Muste.Tree
import Muste.Grammar
import Muste.Grammar.Internal (pgf)
import qualified Muste.Grammar.Internal as Grammar
  ( brackets
  , readPGF
  )
import Muste.AdjunctionTrees

import Muste.Prune

data LinToken = LinToken
  { _ltpath :: Path
  , _ltlin :: String
  , _ltmatched :: Path
  } deriving (Show)

instance Eq LinToken where
  (==) = (==) `on` _ltlin

instance Ord LinToken where
  compare = compare `on` _ltlin

instance FromJSONKey LinToken

instance ToJSONKey LinToken

-- FIXME Better name
-- TODO Merge with `OldL`.
newtype Linearization = Linearization [LinToken] deriving
  ( Show, FromJSON, ToJSON, Semigroup, Monoid
  , Ord, Eq, FromJSONKey, ToJSONKey
  )

-- | Remember all 'AdjunctionTrees' in a certain 'PGF.Language' for a
-- certain 'Grammar'.
data Context = Context
  { ctxtGrammar :: Grammar
  , _ctxtLang   :: PGF.Language
  , ctxtPrecomputed :: AdjunctionTrees
  }

type OldLinearization = [OldL]

{-# DEPRECATED OldL "Being merged with Linearization" #-}
-- | A linearization of a tree is the way a @TTree@ is represented in
-- a given language.  It represents the way the sentence is read.
data OldL = OldL
  { _lpath :: Path
  , _llin :: String
  } deriving (Show,Eq)

-- FIXME Is this right? I copied this from
-- @Muste.getPrunedSuggestions@ So that I could make 'OldL'
-- abstract.
-- | Convert a 'LinToken' to a 'OldL'.
mkOldL :: Linearization -> OldLinearization
mkOldL (Linearization xs) = go <$> xs
  where
  go (LinToken p l _) = OldL p l

instance FromJSON OldL where
  parseJSON = withObject "Linearization" $ \v -> OldL
    <$> v .: "path"
    <*> v .: "lin"

instance ToJSON OldL where
  toJSON (OldL path lin) = object
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
linearizeTreeAux :: Context -> TTree -> Linearization
linearizeTreeAux (Context grammar language _) ttree =
  let
    brackets = Grammar.brackets grammar language ttree
  in
    if not (isEmptyGrammar grammar)
      && language `elem` PGF.languages (pgf grammar)
      && not (null brackets)
    then bracketsToTuples ttree $ head brackets
    else Linearization $ [LinToken [] "?0" []]


-- @CostTree@'s use @OldLinearization@ and not 'Linearization' as
-- returned by 'linearizeTreeAux'.
linearizeTree :: Context -> TTree -> OldLinearization
linearizeTree ctxt tree = mkOldL
  $ linearizeTreeAux ctxt tree

-- | Given a file path creates a mapping from the an identifier of the
-- language to the 'Context' of that language.
langAndContext :: FilePath -> IO [(String, Context)]
langAndContext nm = readLangs <$> Grammar.readPGF nm

readLangs :: Grammar -> [(String, Context)]
readLangs grammar = mkCtxt <$> PGF.languages (pgf grammar)
  where
  mkCtxt lang = (PGF.showCId lang, buildContext grammar lang)


-- This part of the module knows about 'PGF' and maybe shouldn't.  The
-- problem is that 'LinToken' is introduced here and so cannot be
-- placed in 'Muste.Grammar.Internal' without having to move that as
-- well.

-- | Convert a 'PGF.BracketedString' to a list of string/path tuples.
bracketsToTuples :: TTree -> PGF.BracketedString -> Linearization
bracketsToTuples tree bs = deep tree bs
  where
  deep :: TTree -> PGF.BracketedString -> Linearization
  deep _     (PGF.Bracket _ _   _ _ _ []) = mempty
  -- Ordinary leaf
  deep ltree (PGF.Bracket _ fid _ _ _ [PGF.Leaf token]) =
    Linearization $ [LinToken (getPath ltree fid) token []]
  -- Meta leaf
  deep ltree (PGF.Bracket _ fid _ _ [PGF.EMeta id] _) =
    Linearization $ [LinToken (getPath ltree fid) ("?" ++ show id) []]
  -- In the middle of the tree
  deep ltree (PGF.Bracket _ fid _ _ _ bs) =
    broad ltree fid bs mempty
  deep _ _ = error "Muste.linearizeTree: Non-exhaustive pattern match"
  broad :: TTree -> Int -> [PGF.BracketedString] -> Linearization -> Linearization
  -- End of node siblings
  broad _     _   []                 ts = ts
  -- Syncategorial word
  broad ltree fid (PGF.Leaf token:bss) ts = Linearization (x:xs)
    where
    x = LinToken (getPath ltree fid) token []
    Linearization xs = broad ltree fid bss ts
  -- In the middle of the nodes
  broad ltree fid (bs:bss)
    ts = deep ltree bs <> broad ltree fid bss ts

-- | @'matchTk' t0 t1 tk@ checks if a 'LinToken' matches both trees
-- @t0@ and @t1@ and creates a new 'LinToken' indicating this.
matchTk :: TTree -> TTree -> LinToken -> LinToken
matchTk srcTree trgTree (LinToken path lin _)
    = LinToken path lin (matched path srcTree trgTree)

-- | Checks if a linearization token matches in both trees.  If they
-- don't match, then the empty path is returned.
matched :: Path -> TTree -> TTree -> Path
matched p t1 t2 = if selectNode t1 p == selectNode t2 p then p else []

mkLin
  :: Context
  -> TTree
  -> TTree
  -> TTree -- ^ The actual tree to linearize
  -> Linearization
mkLin ctxt srcTree trgTree tree
  = Linearization $ matchTk srcTree trgTree <$> xs
  where
    (Linearization xs) = linearizeTreeAux ctxt tree
