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
import Ajax
import qualified Data.Map.Strict as M
type LinToken = (Path,String)
type Pos = Int

--
-- Data
exampleLang = "PrimaEng" ;
exampleTree = "(useS (useCl (simpleCl (usePron he_PP) (complA Romanus_A))))";
exampleLin = [([0,0,0,0],"he"),([0,0,1],"is"),([0,0,1,0],"Roman")]
exerciseLang = "PrimaLat" ;
exerciseTree = "useS (useCl (simpleCl (usePN Augustus_PN) (complA laetus_A)))";
exerciseLin = [([0,0,0,0],"Augustus"),([0,0,1,0],"laetus"),([0,0,1],"est")]
url = "http://localhost:8080/cgi"

--
-- GUI Logic

-- Main function that sets up everything
musteMain :: ServerMessage -> IO ()
musteMain sm =
  do
    -- Global handlers
    onEvent documentBody Haste.Events.Click globalClickHandler
    Just menu <- elemById "menuButton"
    onEvent menu Haste.Events.Click (menuClickHandler menu sm)
    -- Print target tree
    writeLog (S.fromString "Draw example tree")
    drawExampleTree (sgrammar $ sa sm) (slin $ sa sm) (smenu $ sa sm)
    writeLog (S.fromString "Draw exercise tree")
    drawExerciseTree (sgrammar $ sb sm) (slin $ sb sm) (smenu $ sb sm)
    -- Draw score
    drawScore (sscore sm) (ssuccess sm)
    return ()

-- Updates the click counter
drawScore :: Int -> Bool -> IO ()
drawScore score success =
  do
    Just scoreEl <- elemById "score"
    clearChildren scoreEl
    te <- newTextElem (show score)
    setClass scoreEl "won" success
    appendChild scoreEl te

drawExampleTree :: String -> [LinToken] -> Menu -> IO ()
drawExampleTree lang lin (M menu) =
  do
    -- Get element
    Just exampleTreeDiv <- elemById "exampleTree"
    -- Clear content
    clearChildren exampleTreeDiv
    -- Check for debug
    debug <- hasClass exampleTreeDiv "debug"
    -- Show tree as text
    sequence_ $ map (\l@(p,t) -> drawWord exampleTreeDiv lang l (menu M.! p) debug False False ) lin
    return ()

drawWord :: Elem -> String -> LinToken -> [[CostTree]] -> Bool -> Bool -> Bool -> IO ()
drawWord parent lang (p,s) trees debug enableGaps enableEvents =
  do
    when enableGaps
      (do
          gapSpan <- newElem "span" `with` [ attr "class" =: "gap",
                                             attr "path" =: show p
                                           ]
          gapSpanText <- newTextElem " "
          onEvent gapSpan Haste.Events.MouseOver (wordHoverHandler gapSpan)
          onEvent gapSpan Haste.Events.MouseOut (wordHoverHandler gapSpan)
          appendChild gapSpan gapSpanText
          appendChild parent gapSpan
          when enableEvents
            (do
                onEvent gapSpan Haste.Events.Click (wordClickHandler gapSpan lang p True trees )
                return ()
            )
      )
    wordSpan <- newElem "span" `with` [ attr "class" =: "word",
                                        attr "path" =: show p
                                      ]    
    wordSpanText <- newTextElem s
    onEvent wordSpan Haste.Events.MouseOver (wordHoverHandler wordSpan)
    onEvent wordSpan Haste.Events.MouseOut (wordHoverHandler wordSpan)
    appendChild wordSpan wordSpanText
    appendChild parent wordSpan
    when enableEvents
      (do
          onEvent wordSpan Haste.Events.Click (wordClickHandler wordSpan lang p False trees )
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
drawExerciseTree :: String -> [LinToken] -> Menu -> IO ()
drawExerciseTree lang lin (M menu) =
  do
    Just exerciseTreeDiv <- elemById "exerciseTree"
    clearChildren exerciseTreeDiv
    debug <- hasClass exerciseTreeDiv "debug"
    sequence_ $ map (\l@(p,t) -> drawWord exerciseTreeDiv lang l (menu M.! p) debug True True) lin
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
globalClickHandler :: MouseData -> IO ()
globalClickHandler _ =
  do
    -- Delete possible menus
    deleteMenu "suggestionList"
    deleteMenu "menuList"
    
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
wordClickHandler ::  Elem -> String -> Path -> Bool -> [[CostTree]] -> MouseData -> IO ()
wordClickHandler elem lang path extend trees md =
  do
     -- Don't propagate click any further, keeps menu from disappearing immediatelly
    stopPropagation
    -- Compute list position
    let (x,y) = mouseCoords md
    sglobalx <- (getProp elem "offsetLeft")
    let globalx = x + read sglobalx
    sglobaly <- (getProp elem "offsetTop")
    let globaly = y + read sglobaly
   -- writeLog (S.fromString ("Click on (" ++ show globalx ++ "," ++ show globaly ++ ")") ) :: IO () ;
    -- Cleanup of old list
    deleteMenu "suggestionList"
    selectedPath <- fmap read $ getAttr elem "path" :: IO Path
    writeLog (toJSString $ "Selected Path " ++ show selectedPath)
    -- Create new list
    let suggestions = head trees -- we assume we only have one menu 
    sList <- newElem "div" `with` [ attr "id" =: "suggestionList",
                                    attr "class" =: "menu",
                                    style "top" =: (show globaly ++ "px"),
                                    style "left" =: (show globalx ++ "px")
                                  ]
    sequence_ $ map (\(T cost lin tree) -> newMenuPoint sList (unwords $ map snd lin) (suggestionClickHandler selectedPath lin tree) ) suggestions
    appendChild documentBody sList
    return ()

menuClickHandler :: Elem -> ServerMessage -> MouseData -> IO ()
menuClickHandler elem sm _ =
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
    newMenuPoint mList "Toggle Debug" (\_ -> do { Just e1 <- elemById "exampleTree" ; Just e2 <- elemById "exerciseTree"; toggleClass e1 "debug" ; toggleClass e2 "debug" ; drawExerciseTree (sgrammar $ sa sm) (slin $ sa sm) (smenu $ sa sm) ; drawExampleTree (sgrammar $ sb sm) (slin $ sb sm) (smenu $ sb sm) })
    newMenuPoint mList "Reset" (\_ -> do { drawExerciseTree (sgrammar $ sb sm) exerciseLin (smenu $ sb sm) ; drawScore 0 False } )
    appendChild documentBody mList
    return ()

suggestionClickHandler :: Path -> [LinToken] -> String -> MouseData -> IO ()
suggestionClickHandler path lin tree _ =
  do
--     -- Don't propagate click any further, keeps menu from disappearing immediatelly
    stopPropagation
--     -- writeLog (S.fromString ("Click on suggestion") ) :: IO () ;
--     -- Cleanup of suggestion list
--     deleteMenu "suggestionList"
--     ctx <- readIORef context
--     let oldTree = ctxtree ctx
--     let newTree = [] -- TODO 
--     -- writeLog (S.fromString ("Trying to replace " ++ (show $ fromJust $ selectNode (metaTree oldTree) path ) ++ " in " ++ show (metaTree oldTree) ++ " at " ++ show path ++ " with " ++ (show $ metaTree subTree) )) :: IO () ;
--     writeIORef context (Ctx (ctxlang ctx) newTree (totalClicks ctx + 1))
--     when (newTree == sampleTree)
--       (do
--           Just score <- elemById "score"
--           toggleClass score "won"
--           alert . S.fromString $ "Congratulations! You won after " ++ show (totalClicks ctx + 1) ++ " Clicks"
--           )
--     drawScore context
--     drawTree context
    return ()
    
menuHoverHandler :: Elem -> MouseData -> IO ()
menuHoverHandler elem _ =
  do
    toggleClass elem "menuHover"

wordHoverHandler :: Elem -> MouseData -> IO ()
wordHoverHandler elem _ =
  do
    toggleClass elem "wordHover"

--
-- Program Logic

getServerResponse :: ClientMessage -> CIO ServerMessage
getServerResponse cm =
  do
    let cmEncoded = toJSString $ encodeClientMessage cm
    writeLog $ toJSString ("Send client message " ++ show cmEncoded)
    smResult <- ajax (POST cmEncoded) $ toJSString url
    res <- case smResult of {
      Left a -> error "AjaxError" ; 
      Right sm -> do
          writeLog $ toJSString ("Got server response " ++ toString sm)
          smDecoded <- liftIO $ decodeServerMessage sm
          writeLog (S.fromString ("Decoded server message " ++ show smDecoded)) :: CIO ()
          return $ smDecoded
      }
    return res

main :: IO ()
main =
  do
    let cm = CM (-1) (CT exampleLang exampleTree) (CT exerciseLang exerciseTree)
    withResult (getServerResponse cm) musteMain
    return ()
