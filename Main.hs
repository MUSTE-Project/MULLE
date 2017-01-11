import Muste
import Muste.Tree
import Muste.Grammar
import PGF
import Data.Set hiding (null)
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
    mapM_ (\(a,(b,_)) -> putStrLn $ show a ++ ". " ++ b) $ zip [1..] suggestions
    -- do something to the tree
    putStrLn "Which replacement to you want to have?"
    input <- getLine
    let selection = reads input :: ([(Int,String)])
    (_,newTree) <- if (not $ null selection) && ((snd $ head selection) == "") then handleSelection tree path suggestions (fst $ head selection) else handleCommand tree click input 

    return (Just newClick,newTree)

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
    input <- getLine
    let selection = reads input :: [(Int,String)]
    -- (newClick,newTree) <- if not $ null input && (snd $ head input) == "" then trace "1" $ handleClick grammar language tree wordList click (fst $ head input) else if null input then trace "2" $ handleCommand tree click "" else trace "3" $ handleCommand tree click (snd $ head input)
    (newClick,newTree) <- if (not $ null selection) && ((snd $ head selection) == "") then handleClick grammar language tree wordList click (fst $ head selection) else handleCommand tree click input
    loop grammar language newTree newClick
  
main =
  do
    -- load the grammar
    grammar <- pgfToGrammar <$> readPGF grammarFile
    -- modify the tree, use the first language in the grammar. no previous click
    loop grammar (head $ languages $ pgf grammar) startTree Nothing 
    return ()
  
