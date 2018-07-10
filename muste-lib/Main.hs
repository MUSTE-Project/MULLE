-- | I think this is some kind of command line interface for the
-- business logic of the semantic text editor.
module Main (main, loop) where

import Muste
  ( LinToken(LinToken, ltpath, ltlin)
  , Context
  , CostTree(CostTree)
  , buildContext
  -- ^ Menus
  , getCleanMenu
  -- ^ Linearizations
  , Linearization(Linearization, llin, lpath)
  , linearizeTree
  )

import Common

import Muste.Tree
import Muste.Grammar
import PGF
import Data.Maybe
import System.Exit
import Control.Monad
import Data.List (sort, (\\))

import qualified Data.List as List
import qualified Data.Map.Lazy as M
import qualified Muste.Feat as F

sourceTree = "useS (useCl (simpleCl (useCNdefsg (useN civitas_N)) (transV habere_V2 (usePron he_PP))))"
targetTree = "useS (useCl (simpleCl (complexNP multus_Det (useN amicus_N)) (transV habere_V2 (useCNindefsg (useN hostis_N)))))"
sourceLang = mkCId "PrimaLat"
targetLang = mkCId "PrimaSwe"
grammarFile = "../gf/novo_modo/Prima.pgf"

-- sourceTree = "useS (pastS (simpleCl (useCNdefpl (useN Sabinus_N)) (transV amare_V2 (useCNdefpl (useN liber_N)))))"
-- targetTree = "useS (negPastS (simpleCl (useCNdefpl (useN iuvenis_N)) (transV copula_V2 (useCNindefpl (attribCN (useA Romanus_A) (useN liber_N))))))"
-- sourceLang = mkCId "SecundaLat"
-- targetLang = mkCId "SecundaSwe"
-- grammarFile = "../gf/novo_modo/Secunda.pgf"


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
    extendedList = zip [0..] $ if debug || positions then
                                   -- insert "gaps between the words and point the end of the list to the root of the tree
                                   [(ep, es') | (LinToken ep es _) <- list, es' <- [" ", es]] ++ [([], " ")]
                               else [(p, l) | (LinToken p l _) <- list]
  in
    unwords [conditionalString positions ("(" ++ show pos ++ ") ") ++ s ++ conditionalString debug (" " ++ show path) |
             (pos, (path, s)) <- extendedList]

defaultDebug = True

handleSelection :: Bool -> TTree -> Path -> [(String,TTree)] -> Int -> IO (Maybe Click, TTree,Bool)
handleSelection debug _tree _path suggestions selection =
  do
--    when debug $ putStrLn $ show suggestions
    return (Nothing,snd $ suggestions !! ( selection - 1),debug)

handleClick :: Bool -> Context -> TTree -> [LinToken] -> Maybe Click -> Int -> IO (Maybe Click, TTree,Bool)
handleClick debug context@(grammar, _, _) tree wordList click clickPos =
  do
    let newClick = fromJust $ updateClick click clickPos -- that should never be Nothing -> QuickCheck test for updateClick
    -- Compute the path given the click position and click count
    let tokenPos = pos newClick `div` 2
    let path = if tokenPos == length wordList then [] else take (length (ltpath $ wordList !! tokenPos) - (count newClick - 1)) $ ltpath $ wordList !! tokenPos
    putStrLn $ "You clicked on position " ++ show ( pos newClick ) ++ " for the " ++ show ( count newClick ) ++ " time."
    when debug $ putStrLn $ "That gives token no. " ++ show tokenPos
    when debug $ putStrLn $ "The current path is " ++ show path
    -- Get suggestions
    when debug $ putStrLn "Get new suggestions"
    let menu = getCleanMenu context tree
    when debug $ writeFile "menu.txt" $ showCleanMenu context menu
    let suggestions = [(unwords $ map llin lins, gfAbsTreeToTTree grammar (read tree :: Tree)) |
                       costTrees <- getFromMenu menu path, (CostTree _cost lins tree) <- costTrees] :: [(String, TTree)]
    when debug $ forM_ (zip [1..] suggestions) $ \(pos,(lin,tree)) ->
        do putStrLn $ show pos ++ ". " ++ lin ++ " - " ++ showTTree tree
    when debug $ putStrLn "Linearize new suggestions"
    forM_ (zip [1..] suggestions) $ \(a,(b,_)) ->
        do putStrLn $ show a ++ ". " ++ printSuggestion (map ltlin wordList) (words b)
    putStrLn "0. Click again"
    -- do something to the tree
    let cat = getTreeCat $ fromJust $ selectNode tree path
    when debug $ putStrLn $ "The category is " ++ cat ++ "."
    putStrLn $ "Which replacement do you want to have?"
    putStrLn "Just press Enter to go back"
    input <- getLine
    (_, newTree, _) <- case reads input of
                         [(0, "")] -> handleClick debug context tree wordList (Just newClick) clickPos
                         [(n, "")] -> handleSelection debug tree path suggestions n
                         _         -> handleCommand debug tree click input 
    return (Just newClick,newTree,debug)

-- | handle missing pathes in the menu list
getFromMenu :: M.Map Path [[CostTree]] -> Path -> [[CostTree]]
getFromMenu menu path =
  if path `elem` M.keys menu then menu M.! path
  else getFromMenu menu (take (length path -1) path)
       
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
    putStrLn $ "Goal tree is " ++ targetTree
    putStrLn $ "Current tree is " ++ (showTTree tree)
    putStrLn $ linearizeList debug True wordList
    -- Ask for the click
    putStrLn "What position do you want to click on?"
    putStrLn "Just press Enter to reset clicks"
    input <- getLine
    (newClick,newTree,newDebug) <- case reads input of
                                     [(n, "")] -> handleClick debug context tree wordList click n
                                     _         -> handleCommand debug tree Nothing input
    if (showTTree newTree == targetTree) then
        do putStrLn "You matched the trees!"
           return tree
    else
        do loop context newDebug newTree newClick


main =
  do
    -- load the grammar
    when defaultDebug $ putStrLn "Loading grammar"
    grammar <- pgfToGrammar <$> readPGF grammarFile
    let context = buildContext grammar sourceLang
    when defaultDebug $ putStrLn "Starting loop"
    -- modify the tree, use the first language in the grammar. no previous click
    let tree = gfAbsTreeToTTree grammar $ read sourceTree
    let (v,p) = isValid tree
    if not v then
        error $ "Invalid starting tree. Problem in Node " ++ show p
    else
        -- loop context defaultDebug tree Nothing
        printMenu context targetLang tree


printMenu :: Context -> CId -> TTree -> IO ()
printMenu context@(grammar, _, _) _targetLang tree =
    do let menustructure = getCleanMenu context tree
       forM_ (M.toList menustructure) $ \(path, menus) ->
           do let Just subtree = selectNode tree path
              let TNode _ (Fun subcat _) _ = subtree
              let lin = convLinTokens $ linearizeTree context tree
              let tlin = convLinTokens $ linearizeTree context tree
              putStrLn $ showPath path ++ " : " ++ subcat ++ "  -  " ++ showFocusLin path lin ++ "  -  " ++ showFocusLin path tlin ++ "  -  " ++ showTTree subtree
              forM_ menus $ \costtrees ->
                  do putStr $ " (" ++ show (length costtrees) ++ ")"
                     forM_ costtrees $ \(CostTree cost lin ctree) ->
                         do let t = gfAbsTreeToTTree grammar (read ctree)
                            let Just sub = selectNode t path
                            let tlin = convLinTokens $ linearizeTree context t
                            putStrLn $ "\t" ++ show cost ++ "  -  " ++ showFocusLin path lin ++ "  -  " ++ showFocusLin path tlin ++ "  -  " ++ showTTree sub
              putStrLn ""

       let lin = linearizeTree context tree
       putStrLn $ showTTree tree
       putStrLn $ unwords [w | LinToken _ w _ <- lin]
       putStrLn ""
       let cats = List.nub [cat | (F.Function _ (F.Fun cat _)) <- F.getAllRules grammar]
       putStrLn $ show (length cats) ++ " categories:"
       let (_, _, precomputedTrees) = context
       forM_ precomputedTrees $ \(cat, trees) ->
           do putStrLn $ "\t" ++ cat ++ ": " ++ show (length trees) ++ " adjunction trees, max size " ++ show (maximum [countNodes t | t <- trees]) ++ " nodes"
       putStrLn ""

showPath :: Path -> String
showPath p = concatMap show p

showFocusLin :: Path -> [Linearization] -> String
showFocusLin path lin = unwords [wrap (lpath tok) (llin tok) | tok <- lin]
    where wrap p t | path `List.isPrefixOf` p = "<" ++ t ++ ">"
                   | otherwise = t

convLinTokens :: [LinToken] -> [Linearization]
convLinTokens toks = [Linearization path word | LinToken path word _ <- toks]

-- | Removes menu items further up in the tree if they already show up further down
-- | Attention: Assumes that [[CostTree] actually contains only one menu
thoroughlyClean :: [(Path,[[CostTree]])] -> [(Path,[[CostTree]])]
thoroughlyClean [] = []
thoroughlyClean ((p,[ts]):pts) = (p, [ts]) : thoroughlyClean [(pp, [tt \\ ts]) | (pp, [tt]) <- pts]
thoroughlyClean _ = error "Main: Assumption that cost trees only contain one menu was broken."

showCleanMenu :: Context -> M.Map Path [[CostTree]] -> String
showCleanMenu context menu =
    unlines [show path ++ " :\n" ++ unlines [showCostTree context path t | ts <- trees, t <- ts] |
             path <- sort (M.keys menu), let trees = menu M.! path]

showCostTree :: Context -> Path -> CostTree -> String
showCostTree (grammar, _, _) path (CostTree cost lin tree) =
    ("\t" ++ show cost ++ " - " ++
     unwords [w | Linearization _ w <- lin] ++ " - " ++
     (showTTree $ fromJust $ selectNode (gfAbsTreeToTTree grammar (read tree)) path))
