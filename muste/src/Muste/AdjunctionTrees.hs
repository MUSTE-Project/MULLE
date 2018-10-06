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

import Muste.Tree
import Muste.Grammar
import Muste.Grammar.Internal (Rule(Function))
import qualified Muste.Grammar.Internal as Grammar
import Muste.AdjunctionTrees.Internal

#ifdef DIAGNOSTICS
import Muste.Common
import qualified Data.Text.Prettyprint.Doc as Doc
import System.IO.Unsafe

import qualified Muste.Tree.Internal as Tree
#endif

-- * Creating adjunction trees.

data BuilderInfo = BuilderInfo
  { searchDepth ∷ Maybe Int
  , searchSize  ∷ Maybe Int
  }

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
  =   dbg diagnose
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

  bEnv ∷ BuilderEnv
  bEnv = BuilderEnv { builderInfo , ruleGen }

dbg ∷ (a → IO b) → a → a
#ifdef DIAGNOSTICS
dbg f a = unsafePerformIO (f a) `seq` a
#else
dbg _ = identity
#endif

diagnose ∷ AdjunctionTrees → IO ()
#ifdef DIAGNOSTICS
diagnose (AdjunctionTrees adjTrees) = putDocLn $ Doc.sep 
  [ pretty @Text "Tree sizes [(size, nr.trees)]:"
  , indent $ pretty sizes
  , pretty @Text "Tree depths [(depth, nr.trees)]:"
  , indent $ pretty depths
  ]
  where
  trees  ∷  [TTree]
  trees  =  Map.toList adjTrees >>= \(_, ts) → ts
  sizes  ∷  [(Int, Int)]
  sizes  =  Map.toList
         $  Map.fromListWith (+)
         $  (\t0 → (Tree.countNodes t0, 1))
        <$> trees
  depths ∷  [(Int, Int)]
  depths =  Map.toList
         $  Map.fromListWith (+)
         $  (\t0 → (Tree.treeDepth t0, 1))
        <$> trees
  indent =  Doc.indent 2
#else
diagnose = error "Not diagnosing"
#endif

data BuilderEnv = BuilderEnv
  { builderInfo ∷ BuilderInfo
  , ruleGen     ∷ RuleGen
  }

type RuleGen = Category → [Rule]


getAdjTrees :: BuilderEnv -> Category -> [TTree]
getAdjTrees (BuilderEnv (BuilderInfo depthLimit sizeLimit) ruleGen) startCat
    = [ tree | (tree, _, _) <- adjTs startCat 0 0 [] ]
    where adjTs :: Category -> Int -> Int -> [Category] -> [(TTree, Int, [Category])]
          adjTs cat depth size visited =
              (TMeta cat, size, visited) :
              do guard $ cat `notElem` visited
                 guardLimit depthLimit depth
                 guardLimit sizeLimit size
                 Function fun typ@(Fun _ childcats) <- ruleGen cat
                 (children, size', visited') <- adjCs childcats (depth+1) (size+1) (cat : visited)
                 return (TNode fun typ children, size', visited')

          adjCs :: [Category] -> Int -> Int -> [Category] -> [([TTree], Int, [Category])]
          adjCs [] _depth size visited = return ([], size, visited)
          adjCs (cat:cats) depth size visited =
              do (tree, size', visited') <- adjTs cat depth size visited
                 (trees, size'', visited'') <- adjCs cats depth size' visited'
                 return (tree:trees, size'', visited'')

          guardLimit (Just limit) value = guard $ value < limit
          guardLimit Nothing _ = return ()
  

