import Haste
import Haste.Ajax
import Haste.DOM
import Haste.Concurrent
import PGF
import PGF.Internal
import Data.String as S

import Data.Binary(decode)
import Data.ByteString(fromUArray)
import Haste.Binary(getBlobData,toUArray)

loadPGF :: String -> CIO PGF
loadPGF url =
  do blob <- ajax GET (S.fromString url)
     pgf <- case blob of {
       Left a -> error "AjaxError" ; 
       Right blob -> do
           writeLog (S.fromString ("Loaded pgf as Blob "++url))
           blobdata <- getBlobData blob
           writeLog $ toJSString "Got blobdata"
           let bs = fromUArray (toUArray blobdata)
           decode bs
        }
     writeLog (S.fromString ("Loaded "++ show (abstractName pgf)))
     return pgf

showLangs pgf =
  let
    addListElem :: IO Elem -> String -> IO Elem
    addListElem parent text =
      do
        child <- newElem "li"
        newTextElem text >>= appendChild child
        parent >>= (flip appendChild child) 
        parent
  in
    do
      newList <- foldl addListElem (newElem "ul") $ map showCId $ languages pgf
      hl <- newElem "h1"
      newTextElem "Languages" >>= appendChild hl
      appendChild documentBody hl
      appendChild documentBody newList
      return ()
    
main :: CIO ()
main =
  do
    pgf <- loadPGF "http://hackerbrau.se/haste/Foods.pgf"
    showLangs pgf
    return ()
