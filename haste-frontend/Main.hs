module Main where
import Haste
import Haste.Ajax
import Haste.DOM hiding (click)
import Haste.Concurrent
import Haste.Events hiding (Click)
import qualified Haste.Events
import Haste.Foreign
import Haste.Binary(getBlobData,toUArray)

import Data.IORef
import Control.Monad
import Data.String as S
-- import Ajax

type Path = [Int]
type LinToken = (Path,String)
type Pos = Int

data Context = Ctx { language :: String, tree :: String, lin :: [LinToken], path :: Path, totalClicks :: Int}

exampleLang = "PrimaEng" ;
exampleTree = "(useS (useCl (simpleCl (usePron he_PP) (complA Romanus_A))))";
exampleLin = [([0,0,0,0],"he"),([0,0,1],"is"),([0,0,1,0],"Roman")]
exerciseLang = "PrimaLat" ;
exerciseTree = "useS (useCl (simpleCl (usePN Augustus_PN) (complA laetus_A)))";
exerciseLin = [([0,0,0,0],"Augustus"),([0,0,1,0],"laetus"),([0,0,1],"est")]
emptyPath = []

-- Main function that sets up everything
musteMain :: IO ()
musteMain =
  do
    let ctx = Ctx exerciseLang exerciseTree exerciseLin emptyPath 0
    ctxRef <- newIORef ctx
    -- Global handlers
    onEvent documentBody Haste.Events.Click (globalClickHandler ctxRef)
    Just menu <- elemById "menuButton"
    onEvent menu Haste.Events.Click (menuClickHandler menu ctxRef)
    -- Print target tree
    writeLog (S.fromString "Draw example tree")
    drawExampleTree ctxRef
    writeLog (S.fromString "Draw exercise tree")
    drawExerciseTree ctxRef
    return ()

-- Updates the click counter
drawScore :: IORef Context -> IO ()
drawScore context =
  do
    Just score <- elemById "score"
    ctx <- readIORef context
    clearChildren score
    te <- newTextElem (show $ totalClicks ctx)
    appendChild score te

drawExampleTree :: IORef Context -> IO ()
drawExampleTree context =
  do
    -- Get context
    ctx <- readIORef context
    -- Get element
    Just exampleTreeDiv <- elemById "exampleTree"
    -- Clear content
    clearChildren exampleTreeDiv
    -- Check for debug
    debug <- hasClass exampleTreeDiv "debug"
    -- Show tree as text
    sequence_ $ map (\t -> drawWord exampleTreeDiv context t 0 debug False False ) $ exampleLin
    return ()

drawWord :: Elem -> IORef Context -> LinToken -> Pos -> Bool -> Bool -> Bool ->IO ()
drawWord parent context (p,s) pos debug enableGaps enableEvents =
  do
    when enableGaps
      (do
          gapSpan <- newElem "span" `with` [ attr "class" =: "gap" ]
          gapSpanText <- newTextElem " "
          onEvent gapSpan Haste.Events.MouseOver (wordHoverHandler gapSpan)
          onEvent gapSpan Haste.Events.MouseOut (wordHoverHandler gapSpan)
          appendChild gapSpan gapSpanText
          appendChild parent gapSpan
          when enableEvents
            (do
                onEvent gapSpan Haste.Events.Click (wordClickHandler gapSpan context pos p True )
                return ()
            )
      )
    wordSpan <- newElem "span" `with` [ attr "class" =: "word" ]    
    wordSpanText <- newTextElem s
    onEvent wordSpan Haste.Events.MouseOver (wordHoverHandler wordSpan)
    onEvent wordSpan Haste.Events.MouseOut (wordHoverHandler wordSpan)
    appendChild wordSpan wordSpanText
    appendChild parent wordSpan
    when enableEvents
      (do
          onEvent wordSpan Haste.Events.Click (wordClickHandler wordSpan context pos p False)
          return ()
      )
    when debug
      (do
          pathSpan <- newElem "span" `with` [ attr "class" =: "path" ]
          pathSpanText <- newTextElem (show p)
          appendChild pathSpan pathSpanText
          appendChild parent pathSpan
      )

 -- Takes a tree and transforms it into a sequence of spans in a div
drawExerciseTree :: IORef Context -> IO ()
drawExerciseTree context =
  do
    -- Show the linearized tree
    ctx <- readIORef context
    Just exerciseTreeDiv <- elemById "exerciseTree"
    clearChildren exerciseTreeDiv
    debug <- hasClass exerciseTreeDiv "debug"
    sequence_ $ map (\(p,t) -> drawWord exerciseTreeDiv context t p debug True True) $ zip [0..] (lin ctx)
    return ()

-- Removes the suggestion menu
deleteMenu :: String -> IO ()
deleteMenu name =
  do
    oldList <- elemById name
    case oldList of {
      Just e -> do { clearChildren e ; deleteChild documentBody e };
      Nothing -> return ()
      }

-- On any click on body
globalClickHandler :: IORef Context -> MouseData -> IO ()
globalClickHandler context _ =
  do
    -- Delete possible menus
    deleteMenu "suggestionList"
    deleteMenu "menuList"
    -- reset click
    ctx <- readIORef context
    writeIORef context (Ctx (language ctx) (tree ctx) (lin ctx) emptyPath (totalClicks ctx))
    
-- Adds new menu points as divs to a "menu"
newMenuPoint :: Elem -> String -> (MouseData -> IO ()) -> IO ()
newMenuPoint parent name handler =
  do
    te <- newTextElem name
    le <- newElem "div"
    onEvent le Haste.Events.MouseOver (menuHoverHandler le)
    onEvent le Haste.Events.MouseOut (menuHoverHandler le)
    onEvent le Haste.Events.Click handler
    appendChild le te
    appendChild parent le
    return ()
    
-- -- On click on a word
wordClickHandler ::  Elem -> IORef Context -> Pos -> Path -> Bool -> MouseData -> IO ()
wordClickHandler elem context pos path extend md =
  do
     -- Don't propagate click any further, keeps menu from disappearing immediatelly
    stopPropagation
--     ctx <- readIORef context
--     -- update context
--     writeIORef context (Ctx (language ctx) (tree ctx) (totalClicks ctx))
--     -- Compute list position
--     let (x,y) = mouseCoords md
--     sglobalx <- (getProp elem "offsetLeft")
--     let globalx = x + read sglobalx
--     sglobaly <- (getProp elem "offsetTop")
--     let globaly = y + read sglobaly
--    -- writeLog (S.fromString ("Click on (" ++ show globalx ++ "," ++ show globaly ++ ")") ) :: IO () ;
--     -- Cleanup of old list
--     deleteMenu "suggestionList"
--     let selectedPath = [] -- TODO
--     -- Create new list
--     let suggestions = [] -- TODO 
--     sList <- newElem "div" `with` [ attr "id" =: "suggestionList",
--                                     attr "class" =: "menu",
--                                     style "top" =: (show globaly ++ "px"),
--                                     style "left" =: (show globalx ++ "px")
--                                   ]
--     sequence_ $ map (\(s,t) -> newMenuPoint sList s (suggestionClickHandler context selectedPath t) ) suggestions
--     appendChild documentBody sList
    return ()

menuClickHandler :: Elem -> IORef Context -> MouseData -> IO ()
menuClickHandler elem context _ =
  do
    -- Don't propagate click any further, keeps menu from disappearing immediatelly
    stopPropagation
    -- writeLog (S.fromString ("Click on menu") ) :: IO () ;
    x <- (getProp elem "offsetLeft") >>= (return . read) :: IO Int
    y <- (getProp elem "offsetTop")
    -- Cleanup of old list
    deleteMenu "menuList"
    -- Create new list
    mList <- newElem "div" `with` [ attr "id" =: "menuList",
                                    attr "class" =: "menu",
                                    style "top" =: (y++ "px"),
                                    style "left" =: (show (x - 200) ++ "px")
                                  ]
    -- 
    newMenuPoint mList "Toggle Debug" (\_ -> do { Just e1 <- elemById "exampleTree" ; Just e2 <- elemById "exerciseTree"; toggleClass e1 "debug" ; toggleClass e2 "debug" ; drawExerciseTree context ; drawExampleTree context })
    -- Change tree in context for reset and reset click
    ctx <- readIORef context
    resetContext <- newIORef (Ctx (language ctx) exerciseTree exerciseLin emptyPath 0)
    newMenuPoint mList "Reset" (\_ -> do { drawExerciseTree resetContext ; drawScore resetContext; (readIORef resetContext) >>= (writeIORef context) } )
    appendChild documentBody mList
    return ()

-- suggestionClickHandler :: IORef Context -> Path -> String -> MouseData -> IO ()
-- suggestionClickHandler context path subTree _ =
--   do
--     -- Don't propagate click any further, keeps menu from disappearing immediatelly
--     stopPropagation
--     -- writeLog (S.fromString ("Click on suggestion") ) :: IO () ;
--     -- Cleanup of suggestion list
--     deleteMenu "suggestionList"
--     ctx <- readIORef context
--     let oldTree = tree ctx
--     let newTree = [] -- TODO 
--     -- writeLog (S.fromString ("Trying to replace " ++ (show $ fromJust $ selectNode (metaTree oldTree) path ) ++ " in " ++ show (metaTree oldTree) ++ " at " ++ show path ++ " with " ++ (show $ metaTree subTree) )) :: IO () ;
--     writeIORef context (Ctx (language ctx) newTree (totalClicks ctx + 1))
--     when (newTree == sampleTree)
--       (do
--           Just score <- elemById "score"
--           toggleClass score "won"
--           alert . S.fromString $ "Congratulations! You won after " ++ show (totalClicks ctx + 1) ++ " Clicks"
--           )
--     drawScore context
--     drawTree context

menuHoverHandler :: Elem -> MouseData -> IO ()
menuHoverHandler elem _ =
  do
    toggleClass elem "menuHover"

wordHoverHandler :: Elem -> MouseData -> IO ()
wordHoverHandler elem _ =
  do
    toggleClass elem "wordHover"

main :: IO ()
main =
  do
--    let cm = 
--    let init = getServerMessage "" :: CIO PGF
--    withResult init musteMain
    musteMain
    return ()
