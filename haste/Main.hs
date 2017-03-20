import Haste
import Haste.Ajax
import Haste.DOM hiding (click)
import Haste.Concurrent
import Haste.Events hiding (Click)
import qualified Haste.Events
import Haste.Foreign
import Haste.Binary(getBlobData,toUArray)

import PGF
import PGF.Internal hiding (depth)
import Muste
import Muste.Tree
import Muste.Grammar

import Data.String as S
import Data.Binary(decode)
import Data.ByteString(fromUArray)
import Data.List
import Data.Set hiding (null,map)
import Data.Maybe
import Data.IORef

import Control.Monad

sampleTree = (read "{Pred:(Item->Quality->Comment) {These:(Kind->Item) {Fish:Kind}} {Boring:Quality}}")
sampleLang = "FoodsEng"
-- (Comment:9 (Item:6 this (Kind:5 pizza)) is (Quality:8 very (Quality:7 Italian)))
-- Pred (This Pizza) (Very Italian)
--startTree = MetaTTree (read "{Pred:(Item->Quality->Comment) {This:(Kind->Item) {Pizza:Kind}} {Very:(Quality->Quality) {Italian:Quality}}}") empty --MetaTTree (TMeta wildCId) empty
startTree = (read "{Pred:(Item->Quality->Comment) {These:(Kind->Item) {Fish:Kind}} {Italian:Quality}}")
grammarFile = "Foods.pgf"
depth = 3 -- why???
editLang = "FoodsEng"

-- Context info necessary for lots of stuff
data Context = Ctx { grammar :: Grammar, language :: Language, tree :: TTree, click :: Maybe Muste.Click, totalClicks :: Int}

-- Loads a pgf file from an url
loadPGF :: String -> CIO PGF
loadPGF url =
  do blob <- ajax GET (S.fromString url)
     pgf <- case blob of {
       Left a -> error "AjaxError" ; 
       Right blob -> do
           writeLog (S.fromString ("Loaded pgf as Blob "++url)) :: CIO ()
           blobdata <- getBlobData blob
           writeLog $ toJSString "Got blobdata"
           let bs = fromUArray (toUArray blobdata)
           return $ decode bs
        }
     writeLog (S.fromString ("Loaded "++ show (abstractName pgf))) :: CIO ()
     return pgf

-- Main function that sets up everything
musteMain :: PGF -> IO ()
musteMain pgfGrammar =
  do
    -- Initialize Context
    writeLog (S.fromString "Convert grammar")
    let grammar = pgfToGrammar pgfGrammar
    -- let language = head $ languages pgfGrammar
    -- modify the tree, use the first language in the grammar. no previous click
    context <- newIORef (Ctx grammar (mkCId editLang) startTree Nothing 0)
    -- Global handlers
    onEvent documentBody Haste.Events.Click (globalClickHandler context)
    Just menu <- elemById "menuButton"
    onEvent menu Haste.Events.Click (menuClickHandler menu context)
    -- Print target tree
    writeLog (S.fromString "Draw sample tree")
    drawSampleTree context
    writeLog (S.fromString "Draw object tree")
    drawTree context
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

drawSampleTree :: IORef Context -> IO ()
drawSampleTree context =
  do
    -- Get context
    ctx <- readIORef context
    -- Get element
    Just sampleTreeDiv <- elemById "sampleTree"
    -- Clear content
    clearChildren sampleTreeDiv
    -- Check for debug
    debug <- hasClass sampleTreeDiv "debug"
    -- Show tree as text
    sequence_ $ map (\t -> drawWord sampleTreeDiv context t 0 debug False False ) $ linearizeTree (grammar ctx) (mkCId sampleLang) sampleTree
    return ()

drawWord :: Elem -> IORef Context -> LinToken -> Pos -> Bool -> Bool -> Bool ->IO ()
drawWord parent context (p,s) pos debug enableGaps enableEvents =
  do
    when enableGaps
      (do
          gapSpan <- newElem "span" `with` [ attr "class" =: "gap" ]
          gapSpanText <- newTextElem " "
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
drawTree :: IORef Context -> IO ()
drawTree context =
  do
    -- Show the linearized tree
    ctx <- readIORef context
    let wordList = linearizeTree (grammar ctx) (language ctx) (tree ctx)
    -- writeLog (S.fromString $ show wordList) 
    Just editTreeDiv <- elemById "editTree"
    clearChildren editTreeDiv
    debug <- hasClass editTreeDiv "debug"
    sequence_ $ map (\(p,t) -> drawWord editTreeDiv context t p debug True True) $ zip [0..] wordList
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
    -- writeLog (S.fromString "global click" ) :: IO () ;
    -- Delete possible menus
    deleteMenu "suggestionList"
    deleteMenu "menuList"
    -- reset click
    ctx <- readIORef context
    writeIORef context (Ctx (grammar ctx) (language ctx) (tree ctx) Nothing (totalClicks ctx))
    
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
    
-- On click on a word
wordClickHandler ::  Elem -> IORef Context -> Pos -> Path -> Bool -> MouseData -> IO ()
wordClickHandler elem context pos path extend md =
  let
    updateClick :: Maybe Click -> Pos -> Maybe Click
    updateClick click pos =
      let newClick = case click of {
            Nothing -> Click pos 1 ;
            Just (Click p count) -> if p == pos then Click pos (count + 1) else Click pos 1
            }
      in
        Just newClick
  in
    do
      -- Don't propagate click any further, keeps menu from disappearing immediatelly
      stopPropagation
      ctx <- readIORef context
      -- Update click
      let newClick = updateClick (click ctx) pos
      -- update context
      writeIORef context (Ctx (grammar ctx) (language ctx) (tree ctx) newClick (totalClicks ctx))
      -- Compute list position
      let (x,y) = mouseCoords md
      sglobalx <- (getProp elem "offsetLeft")
      let globalx = x + read sglobalx
      sglobaly <- (getProp elem "offsetTop")
      let globaly = y + read sglobaly
      -- writeLog (S.fromString ("Click on (" ++ show globalx ++ "," ++ show globaly ++ ")") ) :: IO () ;
      -- Cleanup of old list
      deleteMenu "suggestionList"
      -- Create new list
      let selectedPath = take (length path + 1 - (count $ fromJust newClick)) path
      -- writeLog (S.fromString ("Full path " ++ show path ++ " with selected path " ++ show selectedPath )) :: IO ()
      writeLog (S.fromString $ "Get suggestions for path " ++ show selectedPath  ++ if extend then " extending" else "")
      let suggestions = getSuggestions (grammar ctx) (language ctx) (tree ctx) selectedPath extend depth
      sList <- newElem "div" `with` [ attr "id" =: "suggestionList",
                                      attr "class" =: "menu",
                                      style "top" =: (show globaly ++ "px"),
                                      style "left" =: (show globalx ++ "px")
                                    ]
      sequence_ $ map (\(s,t) -> newMenuPoint sList s (suggestionClickHandler context selectedPath t) ) suggestions
      appendChild documentBody sList
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
    newMenuPoint mList "Toggle Debug" (\_ -> do { Just e1 <- elemById "editTree" ; Just e2 <- elemById "sampleTree"; toggleClass e1 "debug" ; toggleClass e2 "debug" ; drawTree context ; drawSampleTree context })
    -- Change tree in context for reset and reset click
    ctx <- readIORef context
    resetContext <- newIORef (Ctx (grammar ctx) (language ctx) startTree Nothing 0)
    newMenuPoint mList "Reset" (\_ -> do { drawTree resetContext ; drawScore resetContext; (readIORef resetContext) >>= (writeIORef context) } )
    appendChild documentBody mList
    return ()

suggestionClickHandler :: IORef Context -> Path -> TTree -> MouseData -> IO ()
suggestionClickHandler context path subTree _ =
  do
    -- Don't propagate click any further, keeps menu from disappearing immediatelly
    stopPropagation
    -- writeLog (S.fromString ("Click on suggestion") ) :: IO () ;
    -- Cleanup of suggestion list
    deleteMenu "suggestionList"
    ctx <- readIORef context
    let oldTree = tree ctx
    let newTree = replaceNode oldTree path subTree
    -- writeLog (S.fromString ("Trying to replace " ++ (show $ fromJust $ selectNode (metaTree oldTree) path ) ++ " in " ++ show (metaTree oldTree) ++ " at " ++ show path ++ " with " ++ (show $ metaTree subTree) )) :: IO () ;
    writeIORef context (Ctx (grammar ctx) (language ctx) newTree Nothing (totalClicks ctx + 1))
    when (newTree == sampleTree)
      (do
          Just score <- elemById "score"
          toggleClass score "won"
          alert . S.fromString $ "Congratulations! You won after " ++ show (totalClicks ctx + 1) ++ " Clicks"
          )
    drawScore context
    drawTree context

menuHoverHandler :: Elem -> MouseData -> IO ()
menuHoverHandler elem _ = toggleClass elem "hover"

main :: IO ()
main =
  do
    let pgf = loadPGF grammarFile :: CIO PGF
    withResult pgf musteMain
    return ()
