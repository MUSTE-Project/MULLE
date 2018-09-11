{-# OPTIONS_GHC -Wall -Wno-name-shadowing #-}
-- | Adjunction trees
--
-- Interfacint with 'AdjunctionTrees' is done using the interface for
-- monomorphic map containers.
module Muste.AdjunctionTrees (AdjunctionTrees, getAdjunctionTrees) where

import Prelude ()
import Muste.Prelude
import qualified Data.Containers      as Mono
import Data.Map (Map)
import qualified Data.Map as Map

import Muste.Tree
import Muste.Grammar
import Muste.Grammar.Internal (Rule(Function))
import qualified Muste.Grammar.Internal as Grammar
import Muste.AdjunctionTrees.Internal

-- * Creating adjunction trees.

-- Profiling has shown me that this function is really heavy.  Quoting the relevant bits:
--
-- COST CENTRE                                                               entries  %time %alloc   %time %alloc
--     getAdjunctionTrees                                                    1        0.0    0.0     4.6   10.2
--      getAdjunctionTrees.\                                                 29       0.0    0.2     4.6   10.2
--       getAdjunctionTrees.adjTrees                                         54085    0.6    1.1     4.6   10.0
--        getAdjunctionTrees.adjChildren                                     341021   0.9    2.4     3.1    8.8
--         treeIsRecursive                                                   281519   0.3    0.2     2.3    6.3
--          getMetas                                                         227463   0.8    2.6     1.7    5.1
--           getMetas.getMetas'                                              1184075  1.0    2.6     1.0    2.6
--          getFunctions                                                     62894    0.2    0.6     0.2    1.0
--           getFunctions.getF                                               98140    0.0    0.3     0.0    0.3
--           compare                                                         57024    0.0    0.0     0.0    0.0
--        getAdjunctionTrees.getRulesFor                                     18947    0.9    0.1     0.9    0.1
-- | Finds all 'AdjunctionTrees' from a specified 'Grammar'.  That is;
-- a mapping from a 'Category' to all trees in the specified 'Grammar'
-- that have this type.
getAdjunctionTrees :: Grammar -> AdjunctionTrees
getAdjunctionTrees grammar = Mono.mapFromList
  $ go <$> allCats
  where
  go ∷ Category → (Category, [TTree])
  go cat = (cat, map fst (adjTrees getRulesFor cat []))
  allRules :: Map String [Rule]
  allRules = Map.fromListWith mappend $ catRule <$> Grammar.getAllRules grammar
  catRule ∷ Rule → (String, [Rule])
  catRule r@(Function _ (Fun c _)) = (c, pure r)
  catRule _ = error "Non-exhaustive pattern match"
  allCats :: [String]
  allCats = Map.keys allRules
  getRulesFor :: String -> [Rule]
  getRulesFor cat = Map.findWithDefault mempty cat allRules

-- The next two functions are mutually recursive.
adjTrees :: (Category → [Rule]) → String -> [String] -> [(TTree, [String])]
adjTrees getRulesFor cat visited = (TMeta cat, visited) : do
  guard $ cat `notElem` visited
  (Function fun typ@(Fun _ childcats)) <- getRulesFor cat
  (children, visited') <- adjChildren getRulesFor childcats (cat:visited)
  pure (TNode fun typ children, visited')

adjChildren :: (Category → [Rule]) → [String] -> [String] -> [([TTree], [String])]
adjChildren _getRulesFor [] visited = [([], visited)]
adjChildren getRulesFor (cat:cats) visited = do
  (tree, visited') <- adjTrees getRulesFor cat visited
  guard $ not $ treeIsRecursive tree
  (trees, visited'') <- adjChildren getRulesFor cats visited'
  pure (tree:trees, visited'')

treeIsRecursive :: TTree -> Bool
treeIsRecursive tree@(TNode _ (Fun cat _) children) =
    case Grammar.getMetas tree of
      [] -> cat `elem` [cat' | Function _ (Fun cat' _) <- concatMap Grammar.getFunctions children]
      [cat'] -> cat == cat'
      _ -> False
treeIsRecursive _ = False

