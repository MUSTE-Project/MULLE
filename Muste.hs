{- |
  High level api to the muste backend
-}
module Muste where
import qualified Data.Set as S
import Tree
import Grammar
import PGF
import Debug.Trace
import Data.Maybe
import Data.List

type LinToken = (String,Path)

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
              path = head $ sortBy (\a -> \b -> compare b a) $ map (\(pos,node) -> getPathWithPos id pos node) (zip [0..(length ns)] ns)
            in
              if path /= [] then pos:path
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
    bracketsToTuples (Bracket _ fid _ _ _ [(Leaf token)]) =
      [(token,idToPath fid ttree)]
      -- [(token,[fid])]
    bracketsToTuples (Bracket _ fid _ _ _ bss) =
      concat $ map bracketsToTuples bss
    ttree = metaTree tree
    abstree = ttreeToGFAbsTree ttree
    pgfGrammar = pgf grammar
    brackets = bracketedLinearize pgfGrammar lang abstree
  in
    bracketsToTuples $ head brackets

-- | The 'linearizeList' functions concatenates a token list to a string
linearizeList :: Bool -> [LinToken] -> String
linearizeList debug list =
  if debug then unwords $ map (\(s,p) -> s ++ " " ++ show p) list
  else unwords $ map (\(s,_) -> s) list

-- | The 'getSuggestions' function generates a list of similar trees given a tree and a position in the token list
getSuggestions :: MetaTTree -> Pos -> S.Set String
getSuggestions tree clickPos =
  treesToStrings $ getNewTrees tree clickPos

-- | The 'getNewTrees' function generates a set of related trees given a MetaTTree and a position in a token list 
getNewTrees :: MetaTTree -> Pos -> S.Set MetaTTree
getNewTrees tree clickPos = S.empty -- TODO

-- | The 'treesToStrings' generates a list of strings based on the differences in similar trees
treesToStrings :: S.Set MetaTTree -> S.Set String
treesToStrings trees = S.empty -- TODO
