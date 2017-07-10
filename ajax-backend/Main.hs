module Main where

import Text.JSON
import Data.Either

data ClientTree = CT {
  cgrammar :: String ,
  ctree :: String
  } deriving (Show) ;

instance JSON ClientTree where
  showJSON ct = encJSDict [("grammar",JSString $ toJSString $ cgrammar ct),("tree",JSString $ toJSString $ ctree ct)] 
  readJSON (JSObject o) =
    let
      elems = map (toEither . flip valFromObj o) ["grammar","tree"]
    in
       if all isLeft elems then let ls = lefts elems in Ok $ CT (ls !! 0) (ls !! 1)
       else Error $ combineErrors elems
    where toEither o = case o of { Ok a -> Left a ; Error b -> Right b };
          combineErrors es = unlines $ rights es
  readJSON _ = Error "Not an object"
  
data ClientMessage = CM {
  cscore :: Int ,
  ca :: ClientTree ,
  cb :: ClientTree
  } deriving (Show) ;

instance JSON ClientMessage where
  showJSON cm = encJSDict [("score",JSString $ toJSString $ show $ cscore cm),("A", JSString $ toJSString $ encode $ ca cm),("B", JSString $ toJSString $ encode $ cb cm)] 
  readJSON (JSObject o) =
    let
      elems = map (toEither . flip valFromObj o) ["score","A","B"]
    in
       if all isLeft elems then let ls = lefts elems in Ok $ CM (ls !! 0) (ls !! 1) (ls !! 2)
       else Error $ combineErrors elems
    where toEither o = case o of { Ok a -> Left a ; Error b -> Right b };
          combineErrors es = unlines $ rights es
  readJSON _ = Error "Not an object"
  --   let
  --     score = valFromObj "score" o
  --     a = valFromObj "a" o
  --     b = valFromObj "b" o
  --    in
  --     case (g,t) of {
  --       (Ok (JSString gg),Ok (JSString tt)) -> Ok $ CT (fromJSString gg) (fromJSString tt) ;
  --       (Error e, _) -> Error e ;
  --       (_, Error e) -> Error e
  --       } ;
  -- readJSON _ = Error "Not an object"

data ServerTree = ST {
  grammar :: String ,
  lin :: [String] ,
  menu :: [((Int,Int),[ClientTree])]
  } deriving (Show) ;

data ServerMessage = SM {
  ssuccess :: Bool ,
  sscore :: Int ,
  sa :: ServerTree ,
  sb :: ServerTree
  } deriving (Show) ;
  
main :: IO ()
main = putStrLn "Hello, Haskell!"
