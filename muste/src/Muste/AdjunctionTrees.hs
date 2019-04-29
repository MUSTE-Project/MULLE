{-# OPTIONS_GHC -Wall #-}
{-# Language
 CPP,
 ConstraintKinds,
 DeriveGeneric,
 GeneralizedNewtypeDeriving,
 NamedFieldPuns,
 OverloadedStrings,
 RecordWildCards,
 StandaloneDeriving,
 TypeFamilies
#-}

-- | Adjunction trees
--
-- Interfacint with 'AdjunctionTrees' is done using the interface for
-- monomorphic map containers.
module Muste.AdjunctionTrees
  ( AdjunctionTrees, AdjKey, AdjTree
  , getAdjunctionTrees
  , BuilderInfo(BuilderInfo, searchDepth, searchSize)
  ) where

#ifdef DIAGNOSTICS
import System.IO.Unsafe
import System.CPUTime (getCPUTime)
#endif

import Control.Monad (guard)
import Control.Applicative (Alternative(empty))

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (isPrefixOf)

import Data.Binary (Binary)
import qualified Data.Binary as Binary
import qualified Data.Map.Strict as M
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet

import qualified Data.Containers as Mono
import Data.MonoTraversable
  (GrowingAppend, MonoFoldable, MonoTraversable, MonoFunctor, Element,
   ofoldl', ofoldr, ofoldMap, ofoldr1Ex, ofoldl1Ex', otraverse)

import GHC.Generics (Generic)

import qualified Muste.Tree as Tree
import Muste.Tree (TTree(TNode,TMeta), Category, FunType(Fun))
import Muste.Grammar (Rule(Function), Grammar)
import qualified Muste.Grammar as Grammar


-- * Creating adjunction trees.

data BuilderInfo = BuilderInfo
  { searchDepth :: Maybe Int
  , searchSize  :: Maybe Int
  } deriving (Show, Eq, Ord)

instance Semigroup BuilderInfo where
  BuilderInfo a0 a1 <> BuilderInfo b0 b1
    = BuilderInfo (a0 <+> b0) (a1 <+> b1)
    where
    a <+> b = (+) <$> a <*> b

instance Monoid BuilderInfo where
  mempty = BuilderInfo empty empty

-- | Finds all 'AdjunctionTrees' from a specified 'Grammar'.  That is;
-- a mapping from a 'Category' to all trees in the specified 'Grammar'
-- that have this type.
getAdjunctionTrees :: BuilderInfo -> Grammar -> AdjunctionTrees
getAdjunctionTrees builderInfo@BuilderInfo{..} grammar
    = diagnose builderInfo $
      AdjunctionTrees $
      Map.fromListWith mappend $
      concatMap treesByCat $
      Map.keys allRules
  where
  treesByCat :: Category -> [(AdjKey, [TTree])]
  treesByCat = getAdjTrees bEnv 
  catRule :: Rule -> (Category, [Rule])
  catRule r@(Function _ (Fun c _)) = (c, pure r)
  catRule _ = error "Non-exhaustive pattern match"
  allRules :: Map Category [Rule]
  allRules = Map.fromListWith mappend $ catRule <$> Grammar.getAllRules grammar
  ruleGen :: RuleGen
  ruleGen cat = Map.findWithDefault mempty cat allRules
  defaultTree :: Map Category TTree
  defaultTree = Map.fromList [ (cat, TNode fun typ []) |
                               (cat, rules) <- Map.toList allRules,
                               rule@(Function fun typ) <- rules,
                               isDefaultRule rule ]

  bEnv :: BuilderEnv
  bEnv = BuilderEnv { builderInfo , ruleGen , defaultTree }

diagnose :: BuilderInfo -> AdjunctionTrees -> AdjunctionTrees
#ifdef DIAGNOSTICS
diagnose builderInfo ats@(AdjunctionTrees adjTrees) = unsafePerformIO $ do
  printf ">> Building adjunction trees, %s\n" (show builderInfo)
  time0 <- getCPUTime
  let trees  :: [TTree]     = Map.toList adjTrees >>= \(_, ts) -> ts
  let sizes  :: [(Int,Int)] = Map.toList $ Map.fromListWith (+) $ (\t0 -> (Tree.countNodes t0, 1)) <$> trees
  let depths :: [(Int,Int)] = Map.toList $ Map.fromListWith (+) $ (\t0 -> (Tree.treeDepth  t0, 1)) <$> trees
  printf "   Sizes  [(size, nr.trees)]: %s\n" (show sizes)
  printf "   Depths [(depth,nr.trees)]: %s\n" (show depths)
  printf "   Total number of adj.trees: %d\n" (length trees)
  time1 <- getCPUTime
  let secs :: Float = fromInteger (time1-time0) * 1e-12
  printf "<< Building adjunction trees: %.2f s\n\n" secs
  return ats
#else
diagnose _ = \x -> x
#endif

data BuilderEnv = BuilderEnv
  { builderInfo :: BuilderInfo
  , ruleGen     :: RuleGen
  , defaultTree :: Map Category TTree 
  }

type RuleGen = Category -> [Rule]


-- | A default rule is hard-coded to be a grammar rule whose name starts with "default".
-- The rule is not allowed to have any children.
-- TODO: This is a bit hacky, hoping there is a better solution.
isDefaultRule :: Rule -> Bool
isDefaultRule (Function fun (Fun _cat childcats))
    | "default" `isPrefixOf` Tree.unCategory fun 
        = null childcats ||
          error ("Default rule " ++ show fun ++ ": must have empty children")
isDefaultRule _ = False


getAdjTrees :: BuilderEnv -> Category -> [(AdjKey, [TTree])]
getAdjTrees (BuilderEnv (BuilderInfo depthLimit sizeLimit) ruleGen defaultTree) startCat
    = [ ((startCat, MultiSet.fromList metas), [tree]) | (tree, metas, _) <- adjTs startCat [] 0 0 [] ]
    where adjTs :: Category -> [Category] -> Int -> Int -> [Category] -> [(TTree, [Category], Int)]
          adjTs cat metas depth size visited =
              (TMeta cat, cat:metas, size) :
              case (depth > 0, Map.lookup cat defaultTree) of
                (True, Just tree) -> return (tree, metas, size+1)
                _ -> do guard (depth `less` depthLimit &&
                               size `less` sizeLimit &&
                               cat `notElem` visited)
                        Function fun typ@(Fun _cat childcats) <- ruleGen cat
                        (children, metas', size') <- adjCs childcats metas (depth+1) (size+1) (cat : visited)
                        return (TNode fun typ children, metas', size')

          adjCs :: [Category] -> [Category] -> Int -> Int -> [Category] -> [([TTree], [Category], Int)]
          adjCs [] metas _depth size _visited = return ([], metas, size)
          adjCs (cat:cats) metas depth size visited =
              do (tree, metas', size') <- adjTs cat metas depth size visited
                 (trees, metas'', size'') <- adjCs cats metas' depth size' visited
                 return (tree:trees, metas'', size'')

          value `less` Just limit = value < limit
          _     `less` Nothing    = True
  


----------------------------------------------------------------------

instance Binary a => Binary (MultiSet a) where
  get = MultiSet.fromOccurMap <$> Binary.get
  put = Binary.put . MultiSet.toMap

type AdjKey = (Category, MultiSet Category)
type AdjTree = (AdjKey, TTree)

-- TODO: add (multi)set of the functions in the Adjtree

-- | @AdjunctionTrees@ really is a map from a @Category@ to a set of
-- trees that have this category.
newtype AdjunctionTrees
  = AdjunctionTrees (M.Map AdjKey [TTree])
  deriving (Show, MonoFunctor, Generic, Binary)

type instance Element AdjunctionTrees = [TTree]

instance MonoFoldable AdjunctionTrees where
  ofoldl'    f a (AdjunctionTrees m) = ofoldl' f a m
  ofoldr     f a (AdjunctionTrees m) = ofoldr f a m
  ofoldMap   f (AdjunctionTrees m)   = ofoldMap f m
  ofoldr1Ex  f (AdjunctionTrees m)   = ofoldr1Ex f m
  ofoldl1Ex' f (AdjunctionTrees m)   = ofoldl1Ex' f m

instance MonoTraversable AdjunctionTrees where
  otraverse f (AdjunctionTrees m) = AdjunctionTrees <$> otraverse f m

deriving instance Semigroup AdjunctionTrees

deriving instance Monoid AdjunctionTrees

instance GrowingAppend AdjunctionTrees where

instance Mono.SetContainer AdjunctionTrees where
  type ContainerKey AdjunctionTrees = (Category, MultiSet Category)
  member k     (AdjunctionTrees m) = Mono.member k m
  notMember k  (AdjunctionTrees m) = Mono.notMember k m
  union        (AdjunctionTrees a) (AdjunctionTrees b) = AdjunctionTrees $ a `Mono.union` b
  intersection (AdjunctionTrees a) (AdjunctionTrees b) = AdjunctionTrees $ a `Mono.intersection` b
  difference   (AdjunctionTrees a) (AdjunctionTrees b) = AdjunctionTrees $ a `Mono.difference` b
  keys         (AdjunctionTrees m) = Mono.keys m

instance Mono.IsMap AdjunctionTrees where
  type MapValue AdjunctionTrees = [TTree]
  lookup c       (AdjunctionTrees m) = Mono.lookup c m
  singletonMap c t                   = AdjunctionTrees $ Mono.singletonMap c t
  mapFromList as                     = AdjunctionTrees $ Mono.mapFromList as
  insertMap k vs (AdjunctionTrees m) = AdjunctionTrees $ Mono.insertMap k vs m
  deleteMap k    (AdjunctionTrees m) = AdjunctionTrees $ Mono.deleteMap k m
  mapToList      (AdjunctionTrees m) = Mono.mapToList m
