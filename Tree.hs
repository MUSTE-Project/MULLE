{-# LANGUAGE FlexibleInstances #-}
module Tree where
import PGF hiding (showType)
import PGF.Internal hiding (showType)
import Data.Maybe

class TreeC t where
  showTree :: t -> String
  selectNode :: t -> Path -> Maybe t
  selectBranch :: t -> Int -> Maybe t
  findPath :: t -> t -> Maybe Path

type Pos = Int
type UPos = (Int,Int)
type Path = [Pos]
type UPath = [UPos]

-- GF Abstract Syntax Tree with numbered nodes
data UTree =
  UEApp UTree UTree Pos
  | UEFun CId Pos

-- A more classical looking generic tree 
data GTree = Node CId [GTree]

-- A generic tree with numbered nodes
data UGTree = UNode CId Pos [UGTree]

-- A generic tree with types
data CGTree = CNode CId (Maybe Type) [CGTree]

showType :: Maybe Type -> String
showType Nothing = "NoType"
showType (Just (DTyp hypos id exprs)) = show id

instance Show UTree where
  show (UEApp e1 e2 p) = "(App:" ++ show p ++ " " ++ show e1 ++ " " ++ show e2 ++ ")"
  show (UEFun cid p) = "(Fun:" ++ show p ++ " " ++ show cid ++ ")"

instance Show GTree where
  show (Node name []) = show name;
  show (Node name children) = "(" ++ (show name) ++ " " ++ ( unwords $ map show children ) ++ ")"

instance Show UGTree where
  show (UNode name pos []) = "("++ (show name) ++ ":"  ++ show pos ++ ")";
  show (UNode name pos children) = "(" ++ (show name) ++ ":" ++ show pos ++ " " ++ ( unwords $ map show children ) ++ ")"

instance Show CGTree where
  show (CNode name t []) = "("++ (show name) ++ ":"  ++ showType t ++ ")";
  show (CNode name t children) = "(" ++ (show name) ++ ":" ++ showType t ++ " " ++ ( unwords $ map show children ) ++ ")"
instance TreeC BracketedString where
  -- My version of showBracketedString with slightly different output and primarily used to understand the BracketedString data type
--  showTree :: BString -> String
  showTree (Leaf token) = "\"" ++ token ++ "\""
  showTree (Bracket cat fid lindex fun exps bss) =
    "(" ++ showCId fun ++ ":" ++ showCId cat ++ " " ++ (unwords $ map showTree bss) ++ ")"

  -- Select a node in a BracketedString determined by a path
--  selectNode :: BracketedString -> Path -> Maybe BracketedString
  selectNode t [] = Just t
  selectNode t (pos:rest) =
    let branch = (selectBranch t pos) in
    case branch of {
      Just b ->  selectNode b rest ;
      Nothing -> Nothing
      }
  -- Given a BracketedString, select one of the possible branches determined by an integer
--  selectBranch :: BracketedString -> Int -> Maybe BracketedString
  selectBranch (Leaf token) i
    | i == 0 = Just (Leaf token)
    | otherwise = Nothing
  selectBranch (Bracket cat fid lindex fun exps bss) i
    | i >= length bss = Nothing
    | otherwise = Just (bss !! i)
  
  -- Find a subtree in a BracketedString and return the path to it
--  findPath :: BracketedString -> BracketedString -> Maybe Path
  findPath tree needle =
    let (Bracket cat1 _ _ fun1 _ bss1) = tree
        (Bracket cat2 _ _ fun2 _ bss2) = needle
    in
      if cat1 == cat2 && fun1 == fun2 && map showBracketedString bss1 == map showBracketedString bss2 then Just []
      else
        Nothing --map (\b -> findPath b needle) bss1

instance TreeC Tree where
  showTree = show
  selectNode t p = Nothing
  selectBranch t i = Nothing
  findPath s n = Nothing

instance TreeC UTree where
  showTree = show
  selectNode t p = Nothing
  selectBranch t i = Nothing
  findPath s n = Nothing

instance TreeC GTree where
  showTree = show
  selectNode t p = Nothing
  selectBranch t i = Nothing
  findPath s n = Nothing

instance TreeC UGTree where
  showTree = show
  selectNode t p = Nothing
  selectBranch t i = Nothing
  findPath s n = Nothing

tree2utree :: Tree -> UTree
tree2utree t = 
  let internal :: Tree -> Int -> (Int,UTree)
      internal (EApp e1 e2) i =
        let (d1,ut1) = internal e1 (i+1)
            (d2,ut2) = internal e2 (d1+1)
        in (d2, UEApp ut1 ut2 i)
      internal (EFun id) i =
        (i,UEFun id i)
  in
    snd $ internal t 0

-- path2upath :: UTree -> Path -> Maybe UPath
-- path2upath ut [] = Just []
-- path2upath (UEFun id pos) [0] = Just [pos]
-- path2upath (UEApp e1 e2 pos) (p:rest)
--   | p == 0 = let next = (path2upath e1 rest) in if isJust next then Just (pos:(fromJust next)) else Nothing
--   | p == 1 = let next = (path2upath e2 rest) in if isJust next then Just (pos:(fromJust next)) else Nothing
--   | otherwise = Nothing

-- Creates a generic tree from an abstract syntax tree
tree2gtree :: Tree -> GTree
tree2gtree (EFun f) = Node f []
tree2gtree (EApp e1 e2) =
  let (Node name sts) = tree2gtree e1
      st2 = tree2gtree e2
  in
    (Node name (sts ++ [st2]))

-- Creates a AST from a generic tree
gtree2tree :: GTree -> Tree
gtree2tree (Node name []) = (EFun name)
gtree2tree (Node name ts) =
  let
     nts = map gtree2tree ts
  in
    mkApp name nts

-- Adds numbers to the nodes of a generic trees
gtree2ugtree :: GTree -> UGTree
gtree2ugtree t =
  let internal :: GTree -> Int -> (Int,UGTree)
      internal (Node name []) i = (i,UNode name i [])
      internal (Node name sts) i =
        let (ni,nsts) = internal2 sts i
        in
          (ni,UNode name i nsts)
      internal2 :: [GTree] -> Int -> (Int,[UGTree])
      internal2 [t] i =
        let (ni,nt) = internal t (i+1)
        in
          (ni,[nt])
      internal2 (t:ts) i =
        let
          (ni,nt) = internal t (i+1)
          (li,nts) = internal2 ts ni
        in
          (li,nt:nts)
  in
    snd $ internal t 0

-- Adds categories from a grammar to a generic tree
gtree2cgtree :: GTree -> PGF -> CGTree
gtree2cgtree (Node id []) pgf = (CNode id (functionType pgf id) [])
gtree2cgtree (Node id ts) pgf = (CNode id (functionType pgf id) (map (\t -> gtree2cgtree t pgf) ts))

-- Creates a list of all subtrees with its depth for a CGTree
cgsubtrees :: CGTree -> [(Int,[CGTree])]
cgsubtrees tree =
  let
    internal :: Int -> CGTree -> [(Int,[CGTree])]
    internal depth (CNode id cat []) = []
    internal depth n@(CNode id cat children) =
      let
        ndepth = depth + 1
      in
        (ndepth,children):(concat $ map (internal ndepth) children) 
  in
    internal 0 tree

-- A generic tree with types
data FooTree = FNode CId [(Type,[Type],[Type])] [CGTree]

augment :: PGF -> CGTree -> IO FooTree
augment grammar (CNode id typ children) =
  let
    (hypos1,typeid,exprs1) = unType $ fromJust typ
    functions = functionsByCat grammar typeid
    types = map (fromJust . functionType grammar) functions
    untypes = map (unType ) types
    hypos = map (\(a,_,_) -> a) untypes
  in
    do
      putStrLn $ show types
      return (FNode id [] [])

getfuntype :: PGF -> CId -> [CId]
getfuntype grammar id =
  let
    typ = functionType grammar id
    (hypos,typeid,exprs) = unType $ fromJust typ
    cats = (map (\(_,_,DTyp _ cat _) -> cat) hypos) ++ [typeid]
  in
    do      
      cats

showfuntype :: [CId] -> String
showfuntype cats =
  foldl (\a -> \b -> a ++ " -> " ++ (show b)) (show $ head cats) (tail cats)

