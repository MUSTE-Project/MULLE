{-# LANGUAGE FlexibleInstances #-}
module Tree where
import PGF hiding (showType)
import PGF.Internal hiding (showType)
import Data.Maybe
import Grammar

class TreeC t where
  showTree :: t -> String
--  selectNode :: t -> Path -> Maybe t
--  selectBranch :: t -> Int -> Maybe t
--  findPath :: t -> t -> Maybe Path


type Pos = Int
type Path = [Pos]

-- A generic tree with types
data TTree = TNode CId (Maybe FunType) [TTree]
           | TMeta CId

data MetaTTree = MetaTTree {
  metaTree :: TTree,
  innerNodes :: [(Path,TTree)]
  }
                 
showType :: Maybe Type -> String
showType Nothing = "NoType"
showType (Just (DTyp hypos id exprs)) = show id

instance Show TTree where
  show (TNode name t []) = "("++ (show name) ++ ":"  ++ show t ++ ")";
  show (TNode name t children) = "(" ++ (show name) ++ ":" ++ show t ++ " " ++ ( unwords $ map show children ) ++ ")"
  show (TMeta name) = "(?" ++ show name ++ ")"

instance Show MetaTTree where
  show tree =
    show (metaTree tree) ++ "\n" ++
    unwords (map show (innerNodes tree))
instance TreeC Tree where
  showTree = show
--  selectNode t p = Nothing
--  selectBranch t i = Nothing
--  findPath s n = Nothing

instance TreeC TTree where
  showTree = show
--  selectNode t p = Nothing
--  selectBranch t i = Nothing
--  findPath s n = Nothing


-- path2upath :: UTree -> Path -> Maybe UPath
-- path2upath ut [] = Just []
-- path2upath (UEFun id pos) [0] = Just [pos]
-- path2upath (UEApp e1 e2 pos) (p:rest)
--   | p == 0 = let next = (path2upath e1 rest) in if isJust next then Just (pos:(fromJust next)) else Nothing
--   | p == 1 = let next = (path2upath e2 rest) in if isJust next then Just (pos:(fromJust next)) else Nothing
--   | otherwise = Nothing

-- Creates a generic tree from an abstract syntax tree
treeToTTree :: PGF -> Tree -> TTree
treeToTTree pgf (EFun f) =
  let
    typ = getFunType pgf f
  in
    TNode f typ []
treeToTTree pgf (EApp e1 e2) =
  let
    (TNode name typ sts) = treeToTTree pgf e1
    st2 = treeToTTree pgf e2
  in
    (TNode name typ (sts ++ [st2]))

-- Creates a AST from a generic tree
ttreeToTree :: TTree -> Tree
ttreeToTree (TNode name _ []) = (EFun name)
ttreeToTree (TNode name _ ts) =
  let
     nts = map ttreeToTree ts
  in
    mkApp name nts


-- Creates a list of all subtrees with its depth for a TTree
tSubTrees :: TTree -> [(Int,[TTree])]
tSubTrees tree =
  let
    internal :: Int -> TTree -> [(Int,[TTree])]
    internal depth (TNode id cat []) = []
    internal depth n@(TNode id cat children) =
      let
        ndepth = depth + 1
      in
        (ndepth,children):(concat $ map (internal ndepth) children) 
  in
    internal 0 tree

-- Prune all subtrees to a certain depth
-- prune :: TTree -> Int -> [MetaTTree]
-- prune tree depth =
--   let
--     inner_prune t@(TNode name cat sts) depth path =
--       let
--         (newTree0,subTree0) = makeMeta t 0
--         (newTree1,subTree1) = makeMeta t 1
--       in
--         [MetaTTree (TMeta ((\(Just (Fun c _)) -> c) cat)) [(path,t)]] ++
--         [MetaTTree newTree0 [(path ++ [0],subTree0)]] ++
--         [MetaTTree newTree1 [(path ++ [0],subTree1)]]
      
--     -- inner_prune :: TTree -> Int -> [Int] -> [MetaTTree]
--     -- inner_prune tree 0 path = [MetaTTree tree []]
--     -- inner_prune (TMeta cat) _ path = [MetaTTree (TMeta cat) []]
--     -- inner_prune (TNode name cat sts) depth path =
--     --   let
--     --     mapPruneOverTrees [] _ _ pos = []
--     --     mapPruneOverTrees trees depth path pos =
--     --       let
--     --         npath = path ++ [pos]
--     --         pruned = inner_prune (head trees) depth npath
--     --       in
--     --         pruned ++ (mapPruneOverTrees (tail trees) depth path (pos + 1))
--     --   in
--     --     mapPruneOverTrees sts (depth - 1) path 0
--   in
--     inner_prune tree depth []

-- makeMeta (TNode name typ sts) pos =
--   let
--     subTree = sts !! pos
--     (nSts1,nSts2) = splitAt pos sts
--     meta = TMeta ((\(TNode _ typ _) -> (\(Just (Fun cat _)) -> cat) typ) subTree)
--     nSts = nSts1 ++ (meta:(tail nSts2))
--     newTree = (TNode name typ nSts)
--   in
--     (newTree,subTree)

makeMeta :: MetaTTree -> [Int] -> MetaTTree
makeMeta tree path = tree -- TODO

maxPath :: TTree -> Int -> [Int]
maxPath (TNode maxDepth =
  

prune :: TTree -> Int -> [MetaTTree]
prune tree depth =
  let
    pruneTrees :: [MetaTTree] -> Int -> [MetaTTree]
    pruneTrees trees depth =
      let
        tree = head trees
        dPath = maxPath (metaTree tree) depth
        nTree = makeMeta tree dPath
      in
        nTree : (pruneTrees [nTree] depth) ++ (pruneTrees (tail trees) depth)
  in
    pruneTrees [(MetaTTree tree [])] depth
        

t = (TNode (mkCId "f") (Just (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])) [(TNode (mkCId "a") (Just (Fun (mkCId "A") [])) []),(TNode (mkCId "g") (Just (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")])) [(TNode (mkCId "b") (Just (Fun (mkCId "B") [])) []),(TNode (mkCId "c") (Just (Fun (mkCId "C") [])) [])])])
