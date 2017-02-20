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

import Data.List

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

showLangs :: PGF -> IO ()
showLangs pgf =
  let
    addListElem :: Elem -> String -> IO ()
    addListElem parent text =
      do
        writeLog (S.fromString $ "added " ++ text)
        child <- newElem "li"
        newTextElem text >>= appendChild child
        flip appendChild child parent
        return ()
  in
    do
      writeLog (S.fromString $ show $ map showCId $ languages pgf)
      newList <- newElem "ul"
      sequence_ $ map (addListElem newList) $ map showCId $ languages pgf
      hl <- newElem "h1"
      newTextElem "Languages" >>= appendChild hl
      appendChild documentBody hl
      appendChild documentBody newList
      return ()
    
main :: IO ()
main =
  do
    let pgf = loadPGF "Foods.pgf" :: CIO PGF
    withResult pgf showLangs
    return ()
