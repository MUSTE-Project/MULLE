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
import Muste.Grammar hiding (tree)
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

-- Profiling reveals that this function is really heavy.  Quoting the
-- relevant bits:
--
--                                                                                                                                          individual      inherited
--     COST CENTRE                             MODULE                  SRC                                             no.       entries  %time %alloc   %time %alloc
--     getAdjunctionTrees                      Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:(44,1)-(68,55)     20735          1    1.5    1.8    21.9   36.9
--      compare                                Data.MultiSet           Data/MultiSet.hs:631:3-45                       20767     901887    3.5    8.6     3.5    8.6
--       unMS                                  Data.MultiSet           Data/MultiSet.hs:187:27-30                      20768    1803774    0.0    0.0     0.0    0.0
--      getAdjunctionTrees.treesByMeta         Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:57:3-46            20761     117914    0.0    0.0     2.3    2.6
--       getMetas                              Muste.Grammar.Internal  src/Muste/Grammar/Internal.hs:(206,1)-(208,42)  20770          0    0.3    0.0     2.3    2.6
--        ...
--      getAdjunctionTrees.regroup             Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:55:3-52            20760         16    0.1    0.3     0.1    0.3
--       getAdjunctionTrees.regroup.\          Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:55:33-44           20762     117914    0.0    0.0     0.0    0.0
--      getAdjunctionTrees.treesByCat          Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:59:3-71            20757         16    0.1    0.2    14.5   23.6
--       adjTrees                              Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:(86,1)-(99,12)     20759      58951    0.4    0.3    14.4   23.5
--        adjTrees.step                        Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:(90,5)-(95,75)     20765     125518    0.2    1.2    14.0   23.2
--         adjChildren                         Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:(102,1)-(110,36)   20766     705674    1.4    4.2    13.8   22.0
--          adjChildren.\                      Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:(105,45)-(110,36)  20778     587776    0.4    0.5    12.2   17.8
--           adjChildren.\.go                  Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:109:7-69           20779     587776    0.9    2.1    11.9   17.2
--            adjChildren.\.step               Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:108:7-58           20781     879254    0.2    0.7     0.2    0.7
--            treeIsRecursive                  Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:(113,1)-(132,25)   20780     587776    0.8    0.8    10.7   14.5
--             treeIsRecursive.metas           Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:123:3-31           20793     528841    0.0    0.0     3.2    3.7
--              ...
--             fold                            Data.MultiSet           Data/MultiSet.hs:(511,1)-(512,15)               20800     280847    0.1    0.0     1.3    1.7
--              ...
--             treeIsRecursive.cats            Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:(124,3)-(128,16)   20803     280847    0.3    0.4     4.8    7.5
--              map                            Data.MultiSet           Data/MultiSet.hs:453:1-41                       20807     280847    1.3    2.7     1.3    2.7
--               unMS                          Data.MultiSet           Data/MultiSet.hs:187:27-30                      20808     280847    0.0    0.0     0.0    0.0
--              mconcat                        Data.MultiSet           Data/MultiSet.hs:196:5-20                       20804     280847    0.0    0.0     0.6    0.7
--               ...
--              getFunctions                   Muste.Grammar.Internal  src/Muste/Grammar/Internal.hs:(212,1)-(216,27)  20817          0    0.1    0.0     2.7    3.8
--               ...
--             toAscList                       Data.MultiSet           Data/MultiSet.hs:546:1-24                       20790          0    0.0    0.0     0.5    0.7
--              ...
--             treeIsRecursive.ruleCat         Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:(129,3)-(131,83)   20830          0    0.1    0.0     0.1    0.0
--              treeIsRecursive.ruleCat.\      Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:130:28             20831     585243    0.0    0.0     0.0    0.0
--          getRulesFor                        Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:82:1-29            20785          0    0.0    0.0     0.1    0.0
--           getAdjunctionTrees.ruleGen        Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:68:3-55            20786      34341    0.1    0.0     0.1    0.0
--        getRulesFor                          Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:82:1-29            20763      34357    0.0    0.0     0.0    0.0
--         getAdjunctionTrees.ruleGen          Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:68:3-55            20764         16    0.0    0.0     0.0    0.0
--      getAdjunctionTrees.allCats             Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:66:3-29            20756          1    0.0    0.0     0.0    0.0
--      getAdjunctionTrees.allRules            Muste.AdjunctionTrees   src/Muste/AdjunctionTrees.hs:61:3-79            20736          1    0.0    0.0     0.0    0.0
--       ...

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
  

