{- |
  High level api to the muste backend
-}
module Muste where
import qualified Data.Set as S
import Tree

-- | The 'linearizeTree' function linearizes a MetaTTree to a list of tokens and pathes to the nodes that create it
linearizeTree :: MetaTTree -> [(String,Path)]
linearizeTree tree = [] -- TODO

-- | The 'linearizeList' functions linearizes a token list to a string
linearizeList :: [(String,Path)] -> Bool -> String
linearizeList list debug =
  if debug then unwords $ map (\(s,p) -> s ++ " " ++ show p) list
  else unwords $ map (\(s,_) -> s) list

-- | The 'getSuggestions' function generates a list of suggestions given a tree and a position in the token list
getSuggestions :: MetaTTree -> Pos -> S.Set String
getSuggestions tree clickPos =
  treesToStrings $ getNewTrees tree clickPos

-- | The 'getNewTrees' function generates a set of related trees given a MetaTTree and a position in a token list 
getNewTrees :: MetaTTree -> Pos -> S.Set MetaTTree
getNewTrees tree clickPos = S.empty -- TODO

-- | The 'treesToStrings' generates a list of strings based on the differences in similar trees
treesToStrings :: S.Set MetaTTree -> S.Set String
treesToStrings trees = S.empty -- TODO
