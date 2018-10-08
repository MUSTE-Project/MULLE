{-# OPTIONS_GHC -Wall #-}
{-# Language ConstraintKinds, CPP, OverloadedStrings, NamedFieldPuns,
  RecordWildCards, DuplicateRecordFields #-}
-- | Adjunction trees
--
-- Interfacint with 'AdjunctionTrees' is done using the interface for
-- monomorphic map containers.
module Muste.AdjunctionTrees
  ( AdjunctionTrees
  , getAdjunctionTrees
  , BuilderInfo(..)
  ) where

import Prelude ()
import Muste.Prelude
import Data.Map (Map)
import qualified Data.Map as Map
import Data.MultiSet (MultiSet)
import Data.Text (isPrefixOf)

import Muste.Tree
import Muste.Grammar
import Muste.Grammar.Internal (Rule(Function))
import qualified Muste.Grammar.Internal as Grammar
import Muste.AdjunctionTrees.Internal

import qualified Muste.Tree.Internal as Tree

#ifdef DIAGNOSTICS
import System.IO.Unsafe
import System.CPUTime (getCPUTime)
#endif

-- * Creating adjunction trees.

data BuilderInfo = BuilderInfo
  { searchDepth ∷ Maybe Int
  , searchSize  ∷ Maybe Int
  } deriving Show

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
getAdjunctionTrees ∷ BuilderInfo → Grammar → AdjunctionTrees
getAdjunctionTrees builderInfo@BuilderInfo{..} grammar
  =   diagnose builderInfo
  $   AdjunctionTrees
  $   Map.fromListWith mappend
  $   (>>= regroup)
  $   fmap (fmap treesByMeta)
  <$> treesByCat
  <$> Map.keys allRules
  where
  regroup
    ∷ (Category                      , [(MultiSet Category, [TTree])])
    → [((Category, MultiSet Category), [TTree])]
  regroup (c, xs) = (\(s, ts) → ((c, s), ts)) <$> xs
  treesByMeta ∷ TTree → (MultiSet Category, [TTree])
  treesByMeta t = (Grammar.getMetas t, pure t)
  treesByCat ∷ Category → (Category, [TTree])
  treesByCat cat = (cat, getAdjTrees bEnv cat)
  catRule ∷ Rule → (Category, [Rule])
  catRule r@(Function _ (Fun c _)) = (c, pure r)
  catRule _ = error "Non-exhaustive pattern match"
  allRules ∷ Map Category [Rule]
  allRules = Map.fromListWith mappend $ catRule <$> Grammar.getAllRules grammar
  ruleGen ∷ RuleGen
  ruleGen cat = Map.findWithDefault mempty cat allRules
  defaultTree ∷ Map Category TTree
  defaultTree = Map.fromList [ (cat, TNode fun typ []) |
                               (cat, rules) <- Map.toList allRules,
                               rule@(Function fun typ) <- rules,
                               isDefaultRule rule ]

  bEnv ∷ BuilderEnv
  bEnv = BuilderEnv { builderInfo , ruleGen , defaultTree }

diagnose ∷ BuilderInfo → AdjunctionTrees → AdjunctionTrees
#ifdef DIAGNOSTICS
diagnose builderInfo ats@(AdjunctionTrees adjTrees) = unsafePerformIO $ do
  printf ">> Building adjunction trees, %s\n" (show builderInfo)
  time0 <- getCPUTime
  let trees  ∷ [TTree]     = Map.toList adjTrees >>= \(_, ts) → ts
  let sizes  ∷ [(Int,Int)] = Map.toList $ Map.fromListWith (+) $ (\t0 → (Tree.countNodes t0, 1)) <$> trees
  let depths ∷ [(Int,Int)] = Map.toList $ Map.fromListWith (+) $ (\t0 → (Tree.treeDepth  t0, 1)) <$> trees
  printf "   Sizes  [(size, nr.trees)]: %s\n" (show sizes)
  printf "   Depths [(depth,nr.trees)]: %s\n" (show depths)
  printf "   Total number of adj.trees: %d\n" (length trees)
  time1 <- getCPUTime
  let secs :: Float = fromInteger (time1-time0) * 1e-12
  printf "<< Building adjunction trees: %.2f s\n\n" secs
  return ats
#else
diagnose = identity
#endif

data BuilderEnv = BuilderEnv
  { builderInfo ∷ BuilderInfo
  , ruleGen     ∷ RuleGen
  , defaultTree ∷ Map Category TTree 
  }

type RuleGen = Category → [Rule]


-- | A default rule is hard-coded to be a grammar rule whose name starts with "default".
-- The rule is not allowed to have any children.
-- TODO: This is a bit hacky, hoping there is a better solution.
isDefaultRule ∷ Rule → Bool
isDefaultRule (Function fun (Fun _cat childcats))
    | "default" `isPrefixOf` Tree.unCategory fun 
        = null childcats ||
          error ("Default rule " ++ show fun ++ ": must have empty children")
isDefaultRule _ = False


getAdjTrees :: BuilderEnv -> Category -> [TTree]
getAdjTrees (BuilderEnv (BuilderInfo depthLimit sizeLimit) ruleGen defaultTree) startCat
    = [ tree | (tree, _) <- adjTs startCat 0 0 [] ]
    where adjTs :: Category -> Int -> Int -> [Category] -> [(TTree, Int)]
          adjTs cat depth size visited =
              (TMeta cat, size) :
              case (depth > 0, Map.lookup cat defaultTree) of
                (True, Just tree) -> return (tree, size+1)
                _ -> do guard (depth `less` depthLimit &&
                               size `less` sizeLimit &&
                               cat `notElem` visited)
                        Function fun typ@(Fun _cat childcats) <- ruleGen cat
                        (children, size') <- adjCs childcats (depth+1) (size+1) (cat : visited)
                        return (TNode fun typ children, size')

          adjCs :: [Category] -> Int -> Int -> [Category] -> [([TTree], Int)]
          adjCs [] _depth size _visited = return ([], size)
          adjCs (cat:cats) depth size visited =
              do (tree, size') <- adjTs cat depth size visited
                 (trees, size'') <- adjCs cats depth size' visited
                 return (tree:trees, size'')

          value `less` Just limit = value < limit
          _     `less` Nothing    = True
  

