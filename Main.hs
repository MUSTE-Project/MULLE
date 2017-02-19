import Muste
import Muste.Tree
import Muste.Grammar
import PGF
import Data.Set hiding (null,map)
import Data.Maybe
import System.Exit
import Debug.Trace

-- (Comment:9 (Item:6 this (Kind:5 pizza)) is (Quality:8 very (Quality:7 Italian)))
-- Pred (This Pizza) (Very Italian)
startTree = MetaTTree (read "{Pred:(Item->Quality->Comment) {This:(Kind->Item) {Pizza:Kind}} {Very:(Quality->Quality) {Italian:Quality}}}") empty --MetaTTree (TMeta wildCId) empty
grammarFile = "gf/Foods.pgf"
depth = 3 -- why???

debug = False

handleSelection :: MetaTTree -> Path -> [(String,MetaTTree)] -> Int -> IO (Maybe Click, MetaTTree)
handleSelection tree path suggestions selection =
  do
    return (Nothing,MetaTTree (replaceNode (metaTree tree) path (metaTree $ snd $ suggestions !! ( selection - 1))) (subTrees tree))
    
handleClick :: Grammar -> Language -> MetaTTree -> [LinToken] -> Maybe Click -> Int -> IO (Maybe Click, MetaTTree)
handleClick grammar language tree wordList click clickPos =
  do
    let newClick = fromJust $ updateClick click clickPos -- that should never be Nothing -> QuickCheck test for updateClick
    -- Compute the path given the click position and click count
    let tokenPos = pos newClick `div` 2
    let path = if tokenPos == length wordList then [] else take (length (fst $ wordList !! tokenPos) - (count newClick - 1)) $ fst $ wordList !! tokenPos
    putStrLn $ "You clicked on position " ++ show ( pos newClick ) ++ " for the " ++ show ( count newClick ) ++ " time. That gives token no. " ++ show tokenPos
    putStrLn $ "The current path is " ++ show path
    let extend = pos newClick `mod` 2 == 0 -- click between words
    -- Get suggestions
    let suggestions = getSuggestions grammar language tree path extend depth 
    -- mapM_ (\(a,(b,_)) -> putStrLn $ show a ++ ". " ++ b) $ zip [1..] suggestions
    let linSubTree = map snd $ linearizeTree grammar language $ makeMeta $ fromJust $ selectNode (metaTree tree) path
    mapM_ (\(a,(b,_)) -> putStrLn $ show a ++ ". " ++ printSuggestion linSubTree (words b)) $ zip [1..] suggestions
    -- do something to the tree
    let cat = getTreeCat $ fromJust $ selectNode (metaTree tree) path
    putStrLn $ "The category is " ++ showCId cat ++ ". Which replacement do you want to have?"
    putStrLn "Just press Enter to go back"
    input <- getLine
    let selection = reads input :: ([(Int,String)])
    (_,newTree) <- if (not $ null selection) && ((snd $ head selection) == "") then handleSelection tree path suggestions (fst $ head selection) else handleCommand tree click input 

    return (Just newClick,newTree)

-- | Takes the linearized old subtree and a new subtree to categorize as and insert, delete or replace
printSuggestion :: [String] -> [String] -> String
printSuggestion oldWords newWords =
  let
    getDiff d1 d2 =
      let (pre,suf) = preAndSuffix d1 d2
      in
        (unwords $ take (length d1 - (length pre + length suf))  $ drop (length pre) d1)
  in
    case compare (length oldWords) (length newWords) of
      -- EQ -> "Replace " ++ (unwords oldWords) ++ " with " ++ (unwords newWords)
      EQ -> "Replace " ++ (getDiff oldWords newWords) ++ " with " ++ (getDiff newWords oldWords)
      -- LT -> "Insert " ++ (unwords $ take (length newWords - (length pre + length suf))  $ drop (length pre) newWords)
      LT -> "Insert " ++ getDiff newWords oldWords
      -- GT -> "Remove " ++ (unwords $ take (length oldWords - (length pre + length suf)) $ drop (length pre)oldWords)
      GT -> "Remove " ++ getDiff oldWords newWords
      
handleCommand :: MetaTTree -> Maybe Click -> String -> IO (Maybe Click,MetaTTree)
handleCommand tree click command
  | command == "" = do return (click,tree)
  | command == "quit" = exitSuccess 
  | otherwise =
    do
      putStrLn "I don't know what you want from me"
      return (click,tree)
loop :: Grammar -> Language -> MetaTTree -> Maybe Click -> IO MetaTTree
loop grammar language tree click =
  do
    -- Show the linearized tree
    let wordList = linearizeTree grammar language tree
    putStrLn $ linearizeList debug True wordList
    -- Ask for the click
    putStrLn "What position do you want to click on?"
    putStrLn "Just press Enter to reset clicks"
    input <- getLine
    let selection = reads input :: [(Int,String)]
    -- (newClick,newTree) <- if not $ null input && (snd $ head input) == "" then trace "1" $ handleClick grammar language tree wordList click (fst $ head input) else if null input then trace "2" $ handleCommand tree click "" else trace "3" $ handleCommand tree click (snd $ head input)
    (newClick,newTree) <- if (not $ null selection) && ((snd $ head selection) == "") then handleClick grammar language tree wordList click (fst $ head selection) else handleCommand tree Nothing input
    loop grammar language newTree newClick
  
main =
  do
    -- load the grammar
    grammar <- pgfToGrammar <$> readPGF grammarFile
    -- modify the tree, use the first language in the grammar. no previous click
    loop grammar (head $ languages $ pgf grammar) startTree Nothing 
    return ()
  
