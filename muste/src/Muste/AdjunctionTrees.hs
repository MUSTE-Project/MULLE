{-# OPTIONS_GHC -Wall #-}
{-# Language ConstraintKinds #-}
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
import Control.Monad.Reader
import Data.Functor.Identity
import qualified Data.MultiSet as MultiSet

import Muste.Tree
import Muste.Grammar hiding (tree)
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
  go cat = (cat, fst <$> runBuilderI (adjTrees cat []) ruleGen)
  allRules :: Map String [Rule]
  allRules = Map.fromListWith mappend $ catRule <$> Grammar.getAllRules grammar
  catRule ∷ Rule → (String, [Rule])
  catRule r@(Function _ (Fun c _)) = (c, pure r)
  catRule _ = error "Non-exhaustive pattern match"
  allCats :: [String]
  allCats = Map.keys allRules
  ruleGen :: RuleGen
  ruleGen cat = Map.findWithDefault mempty cat allRules

type RuleGen = Category → [Rule]

type Builder m = MonadReader RuleGen m

type BuilderT m a = ReaderT RuleGen m a

type BuilderI a = BuilderT Identity a

runBuilderI ∷ BuilderI a → RuleGen → a
runBuilderI = runReader

getRulesFor ∷ Builder m ⇒ Category → m [Rule]
getRulesFor c = ($ c) <$> ask

-- The next two functions are mutually recursive.
adjTrees :: ∀ m . Builder m ⇒ String -> [String] -> m [(TTree, [String])]
adjTrees cat visited = do
  rules ← getRulesFor cat
  let
    step ∷ Rule → m [(TTree, [Category])]
    step (Function fun typ@(Fun _ childcats)) = do
      adjCs ← adjChildren childcats (cat : visited)
      pure $ do
        (children, visited') ← adjCs
        pure $ (TNode fun typ children, visited')
    step _ = error "AdjunctionTrees.adjTrees: Non-exhaustive pattern match"
  children ← join <$> traverse step rules
  pure $ (TMeta cat, visited) : do
    guard $ cat `notElem` visited
    children

adjChildren :: Builder m ⇒ [Category] -> [Category] -> m [([TTree], [Category])]
adjChildren [] visited = pure [([], visited)]
adjChildren (cat:cats) visited = do
  adjCs ← adjTrees cat visited
  join <$> adjCs `forM` \(tree, visited') → do
    let
      step ∷ ([TTree], [Category]) → ([TTree], [Category])
      step (trees, visited'') = (tree : trees , visited'')
      go xs = do { guard $ not $ treeIsRecursive tree ; step <$> xs }
    go <$> adjChildren cats visited'

treeIsRecursive :: TTree -> Bool
treeIsRecursive tree@(TNode _ (Fun cat _) children)
  -- Given the lazy nature of lists it's probably not a problem to
  -- case on the result of 'toList'.  What's worse is that 'MultiSet'
  -- uses strict maps internally.  So 'metas' will be fully
  -- materialized.
  = case MultiSet.toList metas of
    []     → cat `elem` cats
    [cat'] → cat == cat'
    _      → False
  where
  metas = Grammar.getMetas tree
  cats  = [cat' | Function _ (Fun cat' _) <- concatMap Grammar.getFunctions children]
treeIsRecursive _ = False

