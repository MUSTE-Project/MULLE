import Test.QuickCheck
import Muste.Grammar
-- {-# LANGUAGE FlexibleContexts #-}
-- {-# LANGUAGE FlexibleInstances #-}
-- -- | Click is in the Arbitrary class for QuickCheck
-- instance Arbitrary Click where
--   arbitrary =
--     do
--       pos <- arbitrary
--       count <- arbitrary
--       return $ Click pos count

-- -- A 'FunType' can be generated randomly
instance Arbitrary FunType where
   arbitrary =
     sized newFun -- frequency [(9,sized newFun),(1,return NoType)]
     where
       newFun len = do
         let ids = ['A'..'E']
         cat <- elements ids
         cats <- resize len $ listOf1 $ elements ids
         return $ Fun [cat] (map charToString cats)
       charToString c = [c]

-- -- A 'Rule' can be generated randomly
-- instance Arbitrary Rule where
--   arbitrary =
--     do
--       let ids = ['f'..'z']
--       id <- elements ids
--       funtype <- arbitrary 
--       return $ Function [id] funtype
      
-- instance Arbitrary Grammar where
--   arbitrary =
--     do
--       -- generate list of rules
--       genrules <- fmap (filter (\f -> case f of { (Function _ NoType) -> False ; _ -> True })) $ listOf1 (resize 3 arbitrary)
--       let filterrules = nubBy (\(Function id1 _) (Function id2 _) -> id1 == id2 ) genrules
--       let rules = if not $ null filterrules then filterrules else [(Function "f" (Fun "A" ["A"]))]
--       -- select start category
--       let startCat = getRuleCat $ head rules
--       -- get all the cats on the rhss
--       let allCats = nub $ concat $ map (\(Function _ (Fun _ cats)) -> cats) rules -- Problematic
--       let lexRules = map (\c -> Function (map toLower c) (Fun c [])) allCats
--       return $ Grammar startCat rules lexRules emptyPGF $ mkFEAT (Grammar startCat rules lexRules emptyPGF emptyFeat)

-- arbitraryGFAbsTree :: Grammar -> Int -> Gen GFAbsTree
-- arbitraryGFAbsTree grammar depth =
--   let
--     closure :: Grammar -> Int -> GFAbsTree -> Gen GFAbsTree
--     closure grammar depth tree = return tree
--     -- case 1: only the start symbol => first expansion
--     -- case 2: tree that can still be expanded
--     -- case 3: complete tree of sufficient depth
--       -- | not $ hasMetas tree = return tree
--       -- | otherwise = return tree
--   in
--     do
--       let start = startcat grammar
--       closure grammar depth (mkApp (mkCId start) [])

-- --   do
-- --     let ids = ['a'..'z']
-- --     id <- elements ids
-- --     t1 <- arbitrary
-- --     t2 <- arbitrary
-- --     frequency [(3,return (EApp t1 t2)),(7,return (EFun $ mkCId [id]))]
  
-- -- | A GF abstract syntax tree with types is in Arbitrary class
-- -- instance Arbitrary GFAbsTree where
-- --   arbitrary =
-- --     do
-- --       g <- arbitrary
-- --       arbitraryGFAbsTree g

-- arbitraryTTree :: Grammar -> Int -> Gen TTree
-- arbitraryTTree grammar depth =
--   let
--     closure :: Grammar -> Int -> TTree -> Gen TTree
--     closure grammar depth tree
--       | not $ hasMetas tree = return tree
--       | otherwise = 
--         do
--           -- get all metas
--           let metas = getMetaPaths tree
--           -- get one of the metas
--           (path,cat) <- elements metas
--           -- get all the rules for the meta category
--           let lrules = getRulesList (synrules grammar) [cat]
--           let srules = getRulesList (lexrules grammar) [cat]
--           -- prefer lexical rules
--           rules <- frequency [(8, return lrules), (2, return  srules)]
--           -- get one of the rules but handle the case that the preferred category is empty
--           -- here be dragons, but why?
--           rule <- elements $ if null rules then union lrules srules else rules
--           -- apply rule
--           let ntree = applyRule tree rule [path]
--           -- check tree for validity
--           if maxDepth ntree <= depth then closure grammar depth ntree else closure grammar depth tree
--   in
--     do
--       let start = TMeta (startcat grammar)
--       closure grammar depth start


-- -- | A generic tree with types is in Arbitrary class
-- instance Arbitrary TTree where
--   arbitrary =
--     do
--       g <- arbitrary
--       resize 5 $ sized $ arbitraryTTree g -- temporary resize
