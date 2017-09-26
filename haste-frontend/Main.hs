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
import Data.List

type LinToken = (Path,String)
type Pos = Int

--
-- Data
exampleLang = "PrimaEng" ;
exampleTree = "useS (useCl (simpleCl (usePron he_PP) (complA Romanus_A)))";
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
    drawExampleTree (sgrammar $ sa sm) (slin $ sa sm) (smenu $ sa sm)
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
    when success
      (do
          toggleClass scoreEl "won"
          alert . S.fromString $ "Congratulations! You won after " ++ show score ++ " Clicks"
      )
    appendChild scoreEl te

drawExampleTree :: String -> [LinToken] -> Menu -> IO ()
drawExampleTree lang lin menu =
  do
    -- Get element
    Just exampleTreeDiv <- elemById "exampleTree"
    -- Clear content
    clearChildren exampleTreeDiv
    -- Check for debug
    debug <- hasClass exampleTreeDiv "debug"
    -- Memorize Linearization
    setAttr exampleTreeDiv "lin" (show lin)
    setAttr exampleTreeDiv "lang" lang
    -- Show tree as text
    sequence_ $ map (\l@(p,t) -> drawWord exampleTreeDiv lang l menu debug False False ) lin
    return ()

-- Takes a tree and transforms it into a sequence of spans in a div
drawExerciseTree :: String -> [LinToken] -> Menu -> IO ()
drawExerciseTree lang lin menu =
  do
    -- Get element
    Just exerciseTreeDiv <- elemById "exerciseTree"
    -- Clear content
    clearChildren exerciseTreeDiv
    -- Check for debug
    debug <- hasClass exerciseTreeDiv "debug"
    -- Memorize Linearization and language
    setAttr exerciseTreeDiv "lin" (show lin)
    setAttr exerciseTreeDiv "lang" lang
    -- Show tree as text
    sequence_ $ map (\l@(p,t) -> drawWord exerciseTreeDiv lang l menu debug True True) lin
    return ()

drawWord :: Elem -> String -> LinToken -> Menu -> Bool -> Bool -> Bool -> IO ()
drawWord parent lang (p,s) menu debug enableGaps enableEvents =
  do
    parentId <- getAttr parent "id"
    when enableGaps
      (do
          gapSpan <- newElem "span" `with` [ attr "class" =: "gap",
                                             attr "path" =: show p,
                                             attr "parentId" =: parentId,
                                             attr "clicked" =: (show False)
                                           ]
          gapSpanText <- newTextElem " "
          onEvent gapSpan Haste.Events.MouseOver (wordHoverHandler gapSpan)
          onEvent gapSpan Haste.Events.MouseOut (wordHoverHandler gapSpan)
          appendChild gapSpan gapSpanText
          appendChild parent gapSpan
          when enableEvents
            (do
                onEvent gapSpan Haste.Events.Click (wordClickHandler gapSpan True menu)
                return ()
            )
      )
    wordSpan <- newElem "span" `with` [ attr "class" =: "word",
                                        attr "path" =: show p,
                                        attr "parentId" =: parentId,
                                        attr "clicked" =: (show False)
                                      ]    
    wordSpanText <- newTextElem s
    onEvent wordSpan Haste.Events.MouseOver (wordHoverHandler wordSpan)
    onEvent wordSpan Haste.Events.MouseOut (wordHoverHandler wordSpan)
    appendChild wordSpan wordSpanText
    appendChild parent wordSpan
    when enableEvents
      (do
          onEvent wordSpan Haste.Events.Click (wordClickHandler wordSpan False menu)
          return ()
      )
    when debug
      (do
          pathSpan <- newElem "span" `with` [ attr "class" =: "path" ]
          pathSpanText <- newTextElem (show p)
          appendChild pathSpan pathSpanText
          appendChild parent pathSpan
      )

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
wordClickHandler ::  Elem -> Bool -> Menu -> MouseData -> IO ()
wordClickHandler elem isGap (M menu) md =
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
    -- Get click information
    clicked <- fmap read $ getAttr elem "clicked" :: IO Bool
    clickCount <- if clicked then fmap read $ getAttr elem "clickCount" else return 0 :: IO Int
    -- Get parent
    parentId <- getAttr elem "parentid"
    Just parent <- elemById parentId
    -- Update Clicks
    children <- getChildren parent
    mapM_ (\e -> do { setAttr e "clicked" $ show False; unsetAttr e "clickCount" }) children
    setAttr elem "clicked" $ show True
    setAttr elem "clickCount" $ show (clickCount + 1) -- TODO: check if it will end up at the same path as the previously clicked one 
    -- Get path
    wordPath <- fmap read $ getAttr elem "path" :: IO Path
    let selectedPath = take (length wordPath - clickCount) wordPath
    -- Get old linearization
    olin <- fmap read $ getAttr parent "lin" :: IO [LinToken]
    -- Create new list
    let suggestions = head (menu M.! selectedPath) -- we assume we only have one menu
    writeLog (toJSString $ "Suggestions for path " ++ (show selectedPath) ++ ": " ++ show suggestions)
    sList <- newElem "div" `with` [ attr "id" =: "suggestionList",
                                    attr "class" =: "menu",
                                    style "top" =: (show globaly ++ "px"),
                                    style "left" =: (show globalx ++ "px")
                                  ]
    sequence_ $ map (\(T cost nlin tree) -> newMenuPoint sList (getMenuStr nlin selectedPath) (suggestionClickHandler parent tree) ) $ filter (\(T _ l _) -> l /= olin) suggestions
    appendChild documentBody sList
    return ()
    where
      getMenuStr :: [LinToken] -> Path -> String
      getMenuStr nlin path =
        -- let
        --   (pre,suff) = preAndSuffix nlin olin
        --   dropped = drop (length pre) nlin
        -- in
          -- bind $ unwords $ map snd $ take (length dropped - length suff) dropped
          let res = bind $ unwords $ map snd $ filter (\(p,_) -> isPrefixOf path p) nlin
          in if null res then "∅" else res
      -- Computes the longest common prefix and suffix for linearized trees
      preAndSuffix :: Eq a => [a] -> [a] -> ([a],[a])
      preAndSuffix [] _  = ([],[])
      preAndSuffix _  [] = ([],[])
      preAndSuffix a b =
        let prefix :: Eq a => [a] -> [a] ->([a],[a])
            prefix [] _ = ([],[])
            prefix _ [] = ([],[])
            prefix (a:resta) (b:restb)
              | a == b = let (pre,suf) = prefix resta restb in (a:pre,suf)
              | otherwise = ([],reverse $ postfix (reverse (a:resta)) (reverse (b:restb)))
            postfix :: Eq a => [a] -> [a] -> [a]
            postfix [] _ = []
            postfix _ [] = []
            postfix (a:resta) (b:restb)
              | a == b = let suf = postfix resta restb in (a:suf)
              | otherwise = []
        in
          prefix a b
      -- Concatenates strings on GF BIND operator
      bind [] = []
      bind (' ':'&':'+':' ':rest) = bind rest
      bind (c:rest) = c:(bind rest)


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
    newMenuPoint mList "Toggle Debug" (\_ -> do { Just e1 <- elemById "exampleTree" ; Just e2 <- elemById "exerciseTree"; toggleClass e1 "debug" ; toggleClass e2 "debug" ; drawExerciseTree (sgrammar $ sb sm) (slin $ sb sm) (smenu $ sb sm) ; drawExampleTree (sgrammar $ sa sm) (slin $ sa sm) (smenu $ sa sm) })
    newMenuPoint mList "Reset" (\_ -> do { drawExerciseTree (sgrammar $ sb sm) exerciseLin (smenu $ sb sm) ; drawScore 0 False } )
    appendChild documentBody mList
    return ()

suggestionClickHandler :: Elem -> String -> MouseData -> IO ()
suggestionClickHandler parent tree _ =
  do
    -- Don't propagate click any further, keeps menu from disappearing immediatelly
    stopPropagation
    -- Cleanup of suggestion list
    deleteMenu "suggestionList"
    -- Get language
    lang <- getAttr parent "lang"
    -- Get score
    Just scoreEl <- elemById "score"
    score <- fmap read $ getProp scoreEl "textContent" :: IO Int
    let cm = CM score (CT exampleLang exampleTree) (CT lang tree)
    withResult (getServerResponse cm) musteMain
--    return ()
    
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
          return $ smDecoded
      }
    return res

main :: IO ()
main =
  do
    let cm = CM (-1) (CT exampleLang exampleTree) (CT exerciseLang exerciseTree)
    withResult (getServerResponse cm) musteMain
    return ()
