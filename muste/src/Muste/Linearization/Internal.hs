{-# Language OverloadedStrings
, GeneralizedNewtypeDeriving
, CPP
, StandaloneDeriving
, FlexibleContexts
, TypeFamilies
#-}
module Muste.Linearization.Internal
  ( Context(ctxtGrammar, ctxtPrecomputed)
  , buildContext
  , Linearization
  , LinToken
  , ltpath
  , linearizeTree
  , langAndContext
  , mkLin
  , sameOrder
  ) where

import Data.Aeson
-- This might be the only place we should know of PGF
import qualified PGF
import qualified PGF.Internal as PGF hiding (funs, cats)
import Data.Function (on)
#if MIN_VERSION_base(4,11,0)
#else
import Data.Semigroup (Semigroup((<>)))
#endif
import Data.MonoTraversable
  ( Element, MonoTraversable(..), MonoFunctor
  , MonoFoldable(..), GrowingAppend, MonoPointed
  )
import qualified Data.MonoTraversable as Mono
import qualified Data.MonoTraversable.Unprefixed as Mono
import Data.Sequences (SemiSequence, IsSequence, Index)
import qualified Data.Sequences as Mono

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
  { ltpath :: Path
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
newtype Linearization = Linearization { runLinearization:: [LinToken] }
  deriving
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

type instance Element Linearization = LinToken

deriving instance MonoFunctor Linearization

instance MonoFoldable Linearization where
  ofoldl'    f a (Linearization m) = ofoldl' f a m
  ofoldr     f a (Linearization m) = ofoldr f a m
  ofoldMap   f (Linearization m)   = ofoldMap f m
  ofoldr1Ex  f (Linearization m)   = ofoldr1Ex f m
  ofoldl1Ex' f (Linearization m)   = ofoldl1Ex' f m


instance MonoTraversable Linearization where
  otraverse f (Linearization m) = Linearization <$> otraverse f m

instance MonoPointed Linearization where
  opoint = Linearization . Mono.opoint

instance GrowingAppend Linearization where

instance SemiSequence Linearization where
  type Index Linearization = Int
  intersperse a = Linearization .  Mono.intersperse a . runLinearization
  reverse = Linearization . Mono.reverse . runLinearization
  find p = Mono.find p . runLinearization
  sortBy p = Linearization . Mono.sortBy p . runLinearization
  cons e = Linearization . Mono.cons e . runLinearization
  snoc xs e = Linearization . (`Mono.snoc` e) . runLinearization $ xs

instance IsSequence Linearization where

-- | Memoize all @AjdunctionTrees@ for a given grammar and language.
buildContext :: Grammar -> PGF.Language -> Context
buildContext grammar lang =
  Context grammar lang (getAdjunctionTrees grammar)

-- lin is the full linearization
-- Maybe fits better in the grammar.
-- | The 'linearizeTree' function linearizes a @TTree@ to a list of
-- tokens and paths to the nodes that create it
linearizeTree :: Context -> TTree -> Linearization
linearizeTree (Context grammar language _) ttree =
  let
    brackets = Grammar.brackets grammar language ttree
  in
    if not (isEmptyGrammar grammar)
      && language `elem` PGF.languages (pgf grammar)
      && not (null brackets)
    then bracketsToTuples ttree $ head brackets
    else Linearization $ [LinToken [] "?0" []]

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
    (Linearization xs) = linearizeTree ctxt tree

-- | @'sameOrder' xs ys@ checks to see if the tokens in @xs@ occurs in
-- the same sequence in @ys@.
sameOrder :: Linearization -> Linearization -> Bool
sameOrder (Linearization xs) (Linearization ys) = sameOrder' xs ys

-- If we were feeling fancy we might be able to generalize this from
-- '[]' to any 'Traversable'.
-- | @'sameOrder'' xs ys@ checks to see if the elements in @xs@ occurs
-- in the same sequence in @ys@.
sameOrder' :: Eq a => [a] -> [a] -> Bool
sameOrder' [] _ = True
sameOrder' _ [] = False
sameOrder' (x:xs) yss@(y:ys)
  | x == y    = sameOrder' xs ys
  | otherwise = sameOrder' xs yss
