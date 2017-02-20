import Haste
import Haste.Ajax
import Haste.DOM
import Haste.Concurrent

import PGF
import PGF.Internal
import Muste
import Muste.Tree
import Muste.Grammar

import Data.String as S
import Data.Binary(decode)
import Data.ByteString(fromUArray)
import Haste.Binary(getBlobData,toUArray)
import Data.List
import Data.Set hiding (null,map)

-- (Comment:9 (Item:6 this (Kind:5 pizza)) is (Quality:8 very (Quality:7 Italian)))
-- Pred (This Pizza) (Very Italian)
startTree = MetaTTree (read "{Pred:(Item->Quality->Comment) {This:(Kind->Item) {Pizza:Kind}} {Very:(Quality->Quality) {Italian:Quality}}}") empty --MetaTTree (TMeta wildCId) empty
grammarFile = "Foods.pgf"
depth = 3 -- why???

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
    drawTree grammar language startTree True
    return ()

drawTree :: Grammar -> Language -> MetaTTree -> Bool -> IO ()
drawTree grammar language tree debug =
  let drawWord :: LinToken -> Elem -> Bool -> IO ()
      drawWord (p,s) elem debug =
        do
          wordSpan <- newElem "span" `with` [ attr "class" =: "word" ]
          wordSpanText <- newTextElem
          appendChild wordSpan wordSpanText
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

main :: IO ()
main =
  do
    let pgf = loadPGF grammarFile :: CIO PGF
    withResult pgf musteMain
    return ()
