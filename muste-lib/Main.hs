import Muste
import Muste.Tree
import Muste.Grammar
import PGF
import Data.Maybe
import System.Exit
import Control.Monad

import qualified Data.Map.Lazy as M
startTree = "useS (useCl (simpleCl (usePN Augustus_PN) (intransV dicere_V)))"
startLang = mkCId "PrimaLat"

grammarFile = "../gf/novo_modo/Prima.pgf"
depth = 5 -- performance?

-- | Type for a click that has both a position and a count
data Click = Click { pos :: Int, count :: Int } deriving (Show,Eq)

-- | The function 'updateClick' either increases the counter when the position is the same as the previous one or sets the new position and sets the counter to 1
updateClick :: Maybe Click -> Pos -> Maybe Click
updateClick Nothing pos = Just $ Click pos 1
updateClick (Just (Click pos count)) newPos
  | pos == newPos = Just $ Click pos (count + 1)
  | otherwise = Just $ Click newPos 1

-- | The 'linearizeList' functions concatenates a token list to a string, can contain the pathes for debugging and the positions
linearizeList :: Bool -> Bool -> [LinToken] -> String
linearizeList debug positions list =
  let
    conditionalString :: Bool -> String -> String
    conditionalString True s = s
    conditionalString False _ = ""
    extendedList :: [(Integer, (Path, [Char]))]
    extendedList = zip [0..] $ if debug || positions then concatMap (\e@(LinToken ep es _) -> [(ep," "),(ep,es)]) list ++ [([]," ")] -- insert "gaps between the words and point the end of the list to the root of the tree
                               else map (\(LinToken p l _) -> (p,l)) list 
  in
    unwords $ map (\(pos,(path,s)) -> conditionalString positions ("(" ++ show pos ++ ") ") ++ s ++ conditionalString debug (" " ++ show path)) extendedList

defaultDebug = True

handleSelection :: Bool -> TTree -> Path -> [(String,TTree)] -> Int -> IO (Maybe Click, TTree,Bool)
handleSelection debug tree path suggestions selection =
  do
    when debug $ putStrLn $ show suggestions
    return (Nothing,snd $ suggestions !! ( selection - 1),debug)
    
handleClick :: Bool -> Context -> TTree -> [LinToken] -> Maybe Click -> Int -> IO (Maybe Click, TTree,Bool)
handleClick debug context tree wordList click clickPos =
  do
    let newClick = fromJust $ updateClick click clickPos -- that should never be Nothing -> QuickCheck test for updateClick
    -- Compute the path given the click position and click count
    let tokenPos = pos newClick `div` 2
    let path = if tokenPos == length wordList then [] else take (length (ltpath $ wordList !! tokenPos) - (count newClick - 1)) $ ltpath $ wordList !! tokenPos
    putStrLn $ "You clicked on position " ++ show ( pos newClick ) ++ " for the " ++ show ( count newClick ) ++ " time."
    when debug $ putStrLn $ "That gives token no. " ++ show tokenPos
    when debug $ putStrLn $ "The current path is " ++ show path
    let extend = pos newClick `mod` 2 == 0 -- click between words
    -- Get suggestions
    when debug $ putStrLn "Get new suggestions"
--    let suggestions = concat $ map (\(_,ts) -> map (\(_,l,t) -> (linearizeList False False l,t)) ts) $ filter ((path ==) . fst) $ suggestionFromPrecomputed precomputedTrees tree :: [(String,TTree)]
    -- let suggestions = concat $ map (\(_,ts) -> map (\(_,l,t) -> (linearizeList False False l,t)) ts) $ filter ((path ==) . ltpath) $ getSuggestions context tree :: [(String,TTree)]
    let suggestions = concatMap (map (\(CostTree cost lins tree) -> (unwords $ map llin lins,gfAbsTreeToTTree (fst context) (read tree :: Tree)))) $ getCleanMenu context tree M.! path :: [(String,TTree)]
    when debug $ mapM_ (\(pos,(lin,tree)) -> putStrLn $ show pos ++ ". " ++ lin ++ " - " ++ showTTree tree) $ zip [1..] suggestions
    when debug $ putStrLn "Linearize new suggestions"
    -- let linSubTree = map snd $ linearizeTree grammar language $ fromJust $ selectNode tree path
    mapM_ (\(a,(b,_)) -> putStrLn $ show a ++ ". " ++ printSuggestion (map ltlin wordList) (words b)) $ zip [1..] suggestions
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
loop :: Context -> Bool -> TTree -> Maybe Click -> IO TTree
loop context debug tree click =
  do
    -- Show the linearized tree
    let wordList = linearizeTree context tree
    putStrLn $ linearizeList debug True wordList
    -- Ask for the click
    putStrLn "What position do you want to click on?"
    putStrLn "Just press Enter to reset clicks"
    input <- getLine
    let selection = reads input :: [(Int,String)]
    (newClick,newTree,newDebug) <- if (not $ null selection) && ((snd $ head selection) == "") then handleClick debug context precomputed tree wordList click (fst $ head selection) else handleCommand debug tree Nothing input
    loop context newDebug precomputed newTree newClick
    if (showTTree newTree == targetTree) then do { putStrLn "You matched the trees!" ; return tree }
  
main =
  do
    -- load the grammar
    when defaultDebug $ putStrLn "Loading grammar"
    grammar <- pgfToGrammar <$> readPGF grammarFile
    when defaultDebug $ putStrLn "Starting loop"
    -- modify the tree, use the first language in the grammar. no previous click
    let tree = gfAbsTreeToTTree grammar $ fromJust $ readExpr startTree
    let (v,p) = isValid tree
    let context = (grammar,sourceLang)
--    let precomputedTrees = precomputeTrees context tree
--    if v then loop context defaultDebug precomputedTrees tree Nothing
    if v then loop context defaultDebug tree Nothing
    else error $ "Invalid starting tree. Problem in Node " ++ show p
    return ()               
  
