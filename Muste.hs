{- |
  High level api to the muste backend
-}
module Muste where
import qualified Data.Set as S
import Muste.Tree
import Muste.Grammar
import PGF
import PGF.Internal (Expr(..))
import Debug.Trace
import Data.Maybe
import Data.List

type LinToken = (Path,String)

-- | Type for a click that has both a position and a count
type Count = Int
type Click = (Pos,Count)
    
-- | The 'linearizeTree' function linearizes a MetaTTree to a list of tokens and pathes to the nodes that create it
linearizeTree :: Grammar -> Language -> MetaTTree ->  [LinToken]
linearizeTree grammar lang tree = -- TODO
  let
    -- Convert the BracketedString to the list of string/path tuples
    bracketsToTuples :: LTree -> BracketedString -> [LinToken]
    bracketsToTuples tree bs =
      let
        deep :: LTree -> BracketedString -> [LinToken]
        deep _     (Bracket _ _   _ _ _ []) = []
        -- Ordinary leaf
        deep ltree (Bracket _ fid _ _ _ [(Leaf token)]) =
          [(getPath ltree fid, token)]
        -- Meta leaf
        deep ltree (Bracket _ fid _ _ [n@(EMeta id)] _) =
          [(getPath ltree fid, "?" ++ show id)]
        -- In the middle of the tree
        deep ltree (Bracket _ fid _ _ _ bs) =
          broad ltree fid bs []
        broad :: LTree -> Int -> [BracketedString] -> [LinToken] -> [LinToken]
        -- End of node siblings
        broad _     _   []                 ts = ts
        -- Syncategorial word
        broad ltree fid ((Leaf token):bss) ts =
          let
            b = broad ltree fid bss ts
          in
            (getPath ltree fid, token):b
        -- In the middle of the nodes
        broad ltree fid (bs:bss)           ts =
          let
            d = deep ltree bs
            b = broad ltree fid bss ts
          in
            d ++ b
      in
        deep tree bs

    ttree = metaTree tree
    ltree = ttreeToLTree ttree
    abstree = ttreeToGFAbsTree ttree
    pgfGrammar = pgf grammar
    abstree2 = head $ parse pgfGrammar (mkCId "ABC1") (fromJust $ readType "S") "a a a"
    brackets = bracketedLinearize pgfGrammar lang abstree :: [BracketedString]
  in
    if not $ null brackets then bracketsToTuples ltree $ head brackets else [([],"?0")]
    
-- | The 'linearizeList' functions concatenates a token list to a string
linearizeList :: Bool -> [LinToken] -> String
linearizeList debug list =
  if debug then unwords $ map (\(p,s) -> s ++ " " ++ show p) list
  else unwords $ map (\(_,s) -> s) list

-- | The 'getNewTrees' function generates a set of related trees given a MetaTTree and a path
getNewTrees :: Grammar -> Language -> MetaTTree -> Path -> Int -> S.Set MetaTTree
getNewTrees grammar lang tree path depth =
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
getSuggestions :: Grammar -> Language -> [LinToken] -> MetaTTree -> Click -> Int -> S.Set (String, MetaTTree)
getSuggestions grammar lang tokens tree click depth =
  let
    path = [] -- TODO something like take length - count from path at clickpos
    nTrees = getNewTrees grammar lang tree path depth
    suggestions = treesToStrings grammar lang $ nTrees
  in
    S.empty -- TODO something like zip suggestions (combineTrees tree nTrees)
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
