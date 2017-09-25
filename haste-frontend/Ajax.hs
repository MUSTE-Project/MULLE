{-# LANGUAGE DeriveDataTypeable #-}

module Ajax where

import Control.Exception
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.Map.Strict as Map
import Data.List
import Data.Maybe
import Haste
import Haste.JSON

type Path = [Int]

emptyPath = []

data ClientTree = CT {
  cgrammar :: String,
  ctree :: String
  } deriving (Show) ;
  
data ClientMessage = Null | CM {
  cscore :: Int ,
  ca :: ClientTree ,
  cb :: ClientTree
  } deriving (Show) ;
  
data CostTree = T { cost :: Int , lin :: [(Path,String)] , tree :: String } deriving (Show)
-- lin is the full linearization

data Menu = M (Map.Map Path [[CostTree]]) deriving (Show)

data ServerTree = ST {
  sgrammar :: String ,
  stree :: String,
  slin :: [(Path,String)] ,
  smenu :: Menu
  } deriving (Show) ;

data ServerMessage = SM {
  ssuccess :: Bool ,
  sscore :: Int ,
  sa :: ServerTree ,
  sb :: ServerTree
  } deriving (Show) ;

data ServerMessageException = SME String deriving (Show)

instance Exception ServerMessageException

decodeServerMessage :: JSString -> IO ServerMessage
decodeServerMessage s =
  let
    json = decodeJSON s
  in
    either (\e -> do { writeLog (toJSString $ "Error " ++ toString e) ; throw $ SME $ toString e}) decodeMessage json
  where
    decodeMessage :: JSON -> IO ServerMessage
    decodeMessage j =
      let
        ssuccess = j ~> (toJSString "success")
        sscore = j ~> (toJSString "score")
        sa = j ~> (toJSString "a")
        sb = j ~> (toJSString "b")
      in
        do
          treea <- decodeTree $ fromJust sa
          treeb <- decodeTree $ fromJust sb
          if isJust ssuccess && isJust sscore && isJust sa && isJust sb then
            return $ SM (getJustBool ssuccess) (getJustNum sscore) treea treeb
          else
            do
              writeLog (toJSString "Error decoding message data")
              throw (SME "Error decoding message data")
    decodeTree :: JSON -> IO ServerTree
    decodeTree s =
       let
        sgrammar = s ~> (toJSString "grammar")
        stree = s ~> (toJSString "tree")
        slin = s ~> (toJSString "lin")
        smenu = s ~> (toJSString "menu")
      in
         do
           linlist <- decodeLinList $ fromJust slin
           menu <- decodeMenu $ fromJust smenu
           if isJust sgrammar && isJust stree && isJust slin && isJust smenu then             
             return $ ST (getJustStr sgrammar) (getJustStr stree) linlist menu
           else
             do
               writeLog (toJSString "Error decoding tree data")
               throw (SME "Error decoding tree data")
    decodeLinList :: JSON -> IO [(Path,String)]
    decodeLinList (Arr lst) =
      return $ map (\(Arr [(Arr ps),(Str s)]) -> (map (\(Num n) -> floor n) ps, toString s)) lst
    decodeLinList _ = return []
    decodeMenu :: JSON -> IO Menu
    decodeMenu (Dict d) =
      do
        lst <- sequence $ map (\(p,t) -> do { path <- decodePath p ; trees <- decodeCostTrees t ; return (path,trees)}) (take (length d) d)
        writeLog (toJSString $ "### " ++ show lst)
        return $ M $ if Data.List.null lst then Map.empty else Map.fromList $ lst
    decodePath :: JSString -> IO Path
    decodePath p =
      do
        return $ read $ toString p
    decodeCostTrees (Arr [(Arr a)]) =
      do
        writeLog (toJSString "Array")
        cts <- sequence $ map decodeCostTree a
        return [cts] :: IO [[CostTree]] -- TODO
    decodeCostTrees _ =
      do
        writeLog (toJSString "Other")
        return [] :: IO [[CostTree]] -- TODO
    decodeCostTree :: JSON -> IO CostTree
    decodeCostTree j =
      let
         cost = j ~> (toJSString "score")
         lin = j ~> (toJSString "lin")
         tree = j ~> (toJSString "tree")
      in
        do
          writeLog (toJSString $ "Trying to decode cost tree " ++ show j)
          linlist <- decodeLinList $ fromJust lin
          if isJust cost && isJust lin && isJust tree then
            return $ T (getJustNum cost) linlist (getJustStr tree)
          else
            do
              writeLog (toJSString "Error decoding cost tree data")
              throw (SME "Error decoding cost tree data")
    getJustBool (Just (Bool b)) = b
    getJustNum (Just (Num n)) = floor n
    getJustStr (Just (Str s)) = toString s
encodeClientMessage :: ClientMessage -> JSString
encodeClientMessage cm =
  encodeJSON $ encodeMessage cm
  where
    encodeTree (CT grammar tree) = Dict [(toJSString "grammar", Str $ toJSString grammar),
                                           (toJSString "tree", Str $ toJSString tree)]
    encodeMessage Ajax.Null = Haste.JSON.Null
    encodeMessage (CM score ta tb) = Dict [(toJSString "score", Num $ fromIntegral score),
                                             (toJSString "a", ea),
                                             (toJSString "b", eb)]
      where
        ea = encodeTree ta
        eb = encodeTree tb

