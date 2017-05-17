import Muste
import Muste.Tree
import Muste.Grammar
import PGF
import Data.Set hiding (null,map)
import Data.Maybe
import System.Exit
import Debug.Trace
import Control.Monad

startTree = (read "{Pred:(Item->Quality->Comment) {This:(Kind->Item) {Pizza:Kind}} {Very:(Quality->Quality) {Italian:Quality}}}")
grammarFile = "gf/Foods.pgf"
depth = 3 -- why???

defaultDebug = True

handleSelection :: Bool -> TTree -> Path -> [(String,TTree)] -> Int -> IO (Maybe Click, TTree,Bool)
handleSelection debug tree path suggestions selection =
  do
    when debug $ putStrLn $ show suggestions
    return (Nothing,replaceNode tree path (snd $ suggestions !! ( selection - 1)),debug)
    
handleClick :: Bool ->Grammar -> Language -> TTree -> [LinToken] -> Maybe Click -> Int -> IO (Maybe Click, TTree,Bool)
handleClick debug grammar language tree wordList click clickPos =
  do
    let newClick = fromJust $ updateClick click clickPos -- that should never be Nothing -> QuickCheck test for updateClick
    -- Compute the path given the click position and click count
    let tokenPos = pos newClick `div` 2
    let path = if tokenPos == length wordList then [] else take (length (fst $ wordList !! tokenPos) - (count newClick - 1)) $ fst $ wordList !! tokenPos
    putStrLn $ "You clicked on position " ++ show ( pos newClick ) ++ " for the " ++ show ( count newClick ) ++ " time."
    when debug $ putStrLn $ "That gives token no. " ++ show tokenPos
    when debug $ putStrLn $ "The current path is " ++ show path
    let extend = pos newClick `mod` 2 == 0 -- click between words
    -- Get suggestions
    when debug $ putStrLn "Get new suggestions"
    let suggestions = getSuggestions grammar language tree path extend depth 
    when debug $ mapM_ (\(a,(b,_)) -> putStrLn $ show a ++ ". " ++ b) $ zip [1..] suggestions
    when debug $ putStrLn "Linearize new suggestions"
    let linSubTree = map snd $ linearizeTree grammar language $ fromJust $ selectNode tree path
    mapM_ (\(a,(b,_)) -> putStrLn $ show a ++ ". " ++ printSuggestion linSubTree (words b)) $ zip [1..] suggestions
    -- do something to the tree
    let cat = getTreeCat $ fromJust $ selectNode tree path
    when debug $ putStrLn $ "The category is " ++ cat ++ "."
    putStrLn $ "Which replacement do you want to have?"
    putStrLn "Just press Enter to go back"
    input <- getLine
    let selection = reads input :: ([(Int,String)])
    (_,newTree,_) <- if (not $ null selection) && ((snd $ head selection) == "") then handleSelection debug tree path suggestions (fst $ head selection) else handleCommand debug tree click input 

    return (Just newClick,newTree,debug)

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
      EQ -> "Replace " ++ (getDiff oldWords newWords) ++ " with " ++ (getDiff newWords oldWords)
      LT -> "Insert " ++ getDiff newWords oldWords
      GT -> "Remove " ++ getDiff oldWords newWords
      
handleCommand :: Bool -> TTree -> Maybe Click -> String -> IO (Maybe Click,TTree,Bool)
handleCommand debug tree click command
  | command == "" = do return (click,tree,debug)
  | command == "debug" = do return (click,tree,not debug)
  | command == "help" = do { putStrLn "Valid commands: quit, debug, help" ; return (click,tree,debug) }
  | command == "quit" = exitSuccess 
  | otherwise =
    do
      putStrLn "I don't know what you want from me"
      return (click,tree,debug)
loop :: Grammar -> Language -> Bool -> TTree -> Maybe Click -> IO TTree
loop grammar language debug tree click =
  do
    -- Show the linearized tree
    let wordList = linearizeTree grammar language tree
    putStrLn $ linearizeList debug True wordList
    -- Ask for the click
    putStrLn "What position do you want to click on?"
    putStrLn "Just press Enter to reset clicks"
    input <- getLine
    let selection = reads input :: [(Int,String)]
    --(newClick,newTree) <- if not $ null input && (snd $ head input) == "" then trace "1" $ handleClick grammar language tree wordList click (fst $ head input) else if null input then trace "2" $ handleCommand tree click "" else trace "3" $ handleCommand tree click (snd $ head input)
    (newClick,newTree,newDebug) <- if (not $ null selection) && ((snd $ head selection) == "") then handleClick debug grammar language tree wordList click (fst $ head selection) else handleCommand debug tree Nothing input
    loop grammar language newDebug newTree newClick
    return tree
  
main =
  do
    -- load the grammar
    when defaultDebug $ putStrLn "Loading grammar"
    grammar <- pgfToGrammar <$> readPGF grammarFile
    when defaultDebug $ putStrLn "Starting loop"
    -- modify the tree, use the first language in the grammar. no previous click
    let (v,p) = isValid startTree
    if v then loop grammar (head $ tail $ languages $ pgf grammar) defaultDebug startTree Nothing
    else error $ "Invalid starting tree. Problem in Node " ++ show p
    return ()               
  
