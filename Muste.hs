{- |
  High level api to the muste backend
-}
module Muste where
import qualified Data.Set as S
import Muste.Tree
import Muste.Grammar
import PGF
import Debug.Trace
import Data.Maybe
import Data.List

type LinToken = (Path,String)

-- Constant depth for tree generation
depth = 5

-- Constant for the language
lang = fromJust $ readLanguage "LevelsConc"

-- | The 'linearizeTree' function linearizes a MetaTTree to a list of tokens and pathes to the nodes that create it
linearizeTree :: Grammar -> Language -> MetaTTree ->  [LinToken]
linearizeTree grammar lang tree = -- TODO
  let
    -- Finds a path to a token in a ltree
    getPath :: Int -> LTree -> Path
    getPath id ltree = 
      let
        getPathWithPos :: Int -> Pos -> LTree -> Path
        getPathWithPos id pos (LLeaf) = []
        getPathWithPos id pos (LNode cat nid []) = if nid == id then [pos] else []
        getPathWithPos id pos (LNode cat nid ns) =
          if
            id == nid then [pos]
          else
            let
              path = sortBy (\a -> \b -> compare b a) $ map (\(pos,node) -> getPathWithPos id pos node) (zip [0..(length ns)] ns)
            in
              if not $ null path then pos:(head path)
              else []
      in
        getPathWithPos id 0 ltree
    -- Finds a path to a token in a ttree
    idToPath :: Int -> TTree -> Path
    idToPath id ttree =
      let
        labeledTree =  ttreeToLTree ttree
      in
        getPath id labeledTree
    -- Convert the BracketedString to the list of string/path tuples
    bracketsToTuples :: BracketedString -> [LinToken]
    bracketsToTuples b@(Bracket _ fid _ _ _ []) =
      []
    bracketsToTuples b@(Bracket _ fid _ _ _ [(Leaf token)]) =
      [(idToPath fid ttree, token)]
    bracketsToTuples b@(Bracket _ fid _ _ _ bss) =
      concat $ map bracketsToTuples bss
    ttree = metaTree tree
    abstree = ttreeToGFAbsTree ttree
    pgfGrammar = pgf grammar
    abstree2 = head $ parse pgfGrammar (mkCId "ABC1") (fromJust $ readType "S") "a a a"
    brackets = bracketedLinearize pgfGrammar lang abstree :: [BracketedString]
  in
    if not $ null brackets then bracketsToTuples $ head brackets else [([0],"?0")]
    
-- | The 'linearizeList' functions concatenates a token list to a string
linearizeList :: Bool -> [LinToken] -> String
linearizeList debug list =
  if debug then unwords $ map (\(p,s) -> s ++ " " ++ show p) list
  else unwords $ map (\(_,s) -> s) list

-- | The 'getNewTrees' function generates a set of related trees given a MetaTTree and a position in a token list 
getNewTrees :: Grammar -> [LinToken] -> MetaTTree -> Pos -> S.Set MetaTTree
getNewTrees grammar tokens tree clickPos =
  let
    -- Get Path from token list
    (path,token) = tokens !! clickPos
    -- Get Subtree at Path
    subTree :: TTree
    subTree = fromJust $ selectNode (metaTree tree) path
    -- Get category at path
    cat :: CId
    cat = getTreeCat subTree
    -- Generate Trees with same category
    newTrees :: S.Set MetaTTree
    newTrees = generate grammar cat depth
    -- Filter trees
    -- costList = S.map (match (MetaTTree subtree S.empty)) newTrees
    -- TODO: Something with the costList
    -- Idea: linearize subtree and each of newTrees and then order newTrees according to matching pre- and suffixes
    subTreeLin :: [LinToken]
    subTreeLin = linearizeTree grammar lang $ makeMeta subTree
    -- newTreesLin :: [MetaTTree]
    -- newTreesLin = doFilterMagic subTreeLin $ map (\t -> (t,linearizeTree grammar lang t)) $ S.toList newTrees
    doFilterMagic :: [LinToken] -> [(MetaTTree,[LinToken])] -> [MetaTTree]
    doFilterMagic subTree trees =
      let
        preAndSuffix :: [LinToken] -> [LinToken] -> Int
        preAndSuffix [] _ = 0
        preAndSuffix (a:resta) (b:restb) =
          if a == b then 1 + preAndSuffix resta restb else preAndSuffix (reverse resta) (reverse restb)
        magic :: [LinToken] -> (MetaTTree,[LinToken]) -> (MetaTTree,Int)
        magic subTreeLin (tree,lin) = (tree,preAndSuffix subTreeLin lin)
      in
        map (\t -> fst $ magic subTree t ) $ sortBy (\(_,s1) -> \(_,s2) -> compare s1 s2 ) trees -- be more clever here
        
  in
    S.empty -- TODO

-- | The 'treesToStrings' generates a list of strings based on the differences in similar trees
treesToStrings :: Grammar -> Language -> S.Set MetaTTree -> S.Set String
treesToStrings grammar lang trees =
  S.map (linearizeList False) $ S.map (linearizeTree grammar lang) trees

-- | The 'getSuggestions' function generates a list of similar trees given a tree and a position in the token list
getSuggestions :: Grammar -> Language -> [LinToken] -> MetaTTree -> Pos -> S.Set String
getSuggestions grammar lang tokens tree clickPos =
  treesToStrings grammar lang $ getNewTrees grammar tokens tree clickPos
  
mt = (MetaTTree
      (read "{s:(A -> S) {f:(A -> B -> A) {f:(A -> B -> A) {?A} {g:(B -> C -> B) {?B} {c:C}}} {b:(B)}}")
      $ S.fromList [([0,0], (read "{?A}")),
                  ([0,1], (read "{?B}"))
                 ]
     )
t = (read "{s:(A -> S) {f:(A -> B -> A) {a:A} {b:B}}") :: TTree

t2 = (read "{s:(A -> S) {f:(A -> B -> A) {f:(A -> B -> A) {a:A} {g:(B -> C -> B) {b:B} {c:C}}} {b:(B)}}") :: TTree

t3 = (read "{l0:(Level1 -> Level0) {l1o0:(Level2 -> Level1) {l2:(Token0 -> Token1 -> Token2 -> Level2) {t0:Token0} {t1o0:Token0} {t2:Token2}}}") :: TTree
main =
  do
    pgf <- readPGF "gf/Levels.pgf"
    let grammar = pgfToGrammar pgf
    putStrLn $ show $ ttreeToGFAbsTree t3
    putStrLn $ show $ linearizeTree grammar lang (makeMeta t)
    return ()
