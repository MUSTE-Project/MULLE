import Haste
import Haste.Ajax
import Haste.DOM
import Haste.Concurrent
import Haste.Events
import Haste.Foreign

import PGF
import PGF.Internal hiding (depth)
import Muste
import Muste.Tree
import Muste.Grammar

import Data.String as S
import Data.Binary(decode)
import Data.ByteString(fromUArray)
import Haste.Binary(getBlobData,toUArray)
import Data.List
import Data.Set hiding (null,map)
import Data.Maybe

-- (Comment:9 (Item:6 this (Kind:5 pizza)) is (Quality:8 very (Quality:7 Italian)))
-- Pred (This Pizza) (Very Italian)
startTree = MetaTTree (read "{Pred:(Item->Quality->Comment) {This:(Kind->Item) {Pizza:Kind}} {Very:(Quality->Quality) {Italian:Quality}}}") empty --MetaTTree (TMeta wildCId) empty
grammarFile = "Foods.pgf"
depth = 3 -- why???
debug = True

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

musteMain :: PGF -> IO ()
musteMain pgfGrammar =
  do
    let grammar = pgfToGrammar pgfGrammar
    let language = head $ languages pgfGrammar
    -- modify the tree, use the first language in the grammar. no previous click
    onEvent documentBody Haste.Events.Click globalClickHandler
    drawTree grammar language startTree debug
    return ()

-- Takes a tree and transforms it into a sequence of spans in a div
drawTree :: Grammar -> Language -> MetaTTree -> Bool -> IO ()
drawTree grammar language tree debug =
  let drawWord :: LinToken -> Elem -> Bool -> IO ()
      drawWord (p,s) elem debug =
        do
          gapSpan <- newElem "span" `with` [ attr "class" =: "gap" ]
          gapSpanText <- newTextElem " "
          appendChild gapSpan gapSpanText
          onEvent gapSpan Haste.Events.Click (wordClickHandler grammar language tree p True gapSpan )
          appendChild elem gapSpan
          wordSpan <- newElem "span" `with` [ attr "class" =: "word" ]
          wordSpanText <- newTextElem s
          appendChild wordSpan wordSpanText
          onEvent wordSpan Haste.Events.Click (wordClickHandler grammar language tree p False wordSpan)
          appendChild elem wordSpan
          if debug then
            (do
                pathSpan <- newElem "span" `with` [ attr "class" =: "path" ]
                pathSpanText <- newTextElem (show p)
                appendChild pathSpan pathSpanText
                appendChild elem pathSpan
            )
          else return ()
  in
    do
  -- Show the linearized tree
      let wordList = linearizeTree grammar language tree
      writeLog (S.fromString $ show wordList) 
      Just linTreeDiv <- elemById "linTree"
      sequence_ $ map (\t -> drawWord t linTreeDiv debug) $ wordList
      return ()

-- Removes the suggestion menu
deleteMenu :: IO ()
deleteMenu =
  do
    oldList <- elemById "suggestionList"
    case oldList of {
      Just e -> do { clearChildren e ; deleteChild documentBody e };
      Nothing -> return ()
      }

-- On any click on body
globalClickHandler :: MouseData -> IO ()
globalClickHandler _ =
  do
    writeLog (S.fromString "global click" ) :: IO () ;
    deleteMenu

-- On click on a word
wordClickHandler :: Grammar -> Language -> MetaTTree -> Path -> Bool -> Elem -> MouseData -> IO ()
wordClickHandler grammar language tree path extend elem md =
  do
    stopPropagation
    let (x,y) = mouseCoords md
    sglobalx <- (getProp elem "offsetLeft")
    let globalx = x + read sglobalx
    sglobaly <- (getProp elem "offsetTop")
    let globaly = y + read sglobaly
    
    writeLog (S.fromString ("Click on (" ++ show (globalx + x) ++ "," ++ show (globaly + y) ++ ")") ) :: IO () ;
    -- Cleanup of old list
    deleteMenu
    -- Create new list
    let suggestions = getSuggestions grammar language tree path extend depth
    sList <- newElem "div" `with` [ attr "id" =: "suggestionList",
                                    style "top" =: (show globaly ++ "px"),
                                    style "left" =: (show globalx ++ "px")
                                  ]
    sequence_ $ map (\(s,t) -> do { te <- newTextElem s ; le <- newElem "div" ; onEvent le Haste.Events.MouseOver (menuHoverHandler le); onEvent le Haste.Events.MouseOut (menuHoverHandler le) ; appendChild le te ; appendChild sList le } ) suggestions
    appendChild documentBody sList
    return ();

menuHoverHandler :: Elem -> MouseData -> IO ()
menuHoverHandler elem _ = toggleClass elem "hover"

main :: IO ()
main =
  do
    let pgf = loadPGF grammarFile :: CIO PGF
    withResult pgf musteMain
    return ()
