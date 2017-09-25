{-# LANGUAGE DeriveDataTypeable, OverloadedStrings #-}

module Ajax where

import Data.Aeson
import Data.Aeson.Encoding
import Data.Text (Text(..),pack,unpack)
import Data.Monoid
import Control.Exception
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.Map.Strict as Map
-- import Data.Either
import Data.List
import Data.Maybe
import Muste hiding (linearizeTree)
import Muste.Grammar
import qualified Muste as M
import Muste.Tree
import PGF
import Data.Map hiding (map)
import Data.IORef

data ClientTree = CT {
  cgrammar :: String,
  ctree :: String
  } deriving (Show) ;
  
data ClientMessage = Null | CM {
  cscore :: Int ,
  ca :: ClientTree ,
  cb :: ClientTree
  } deriving (Show) ;
  
instance FromJSON ClientTree where
  parseJSON = withObject "ClientTree" $ \v -> CT
    <$> v .: "grammar"
    <*> v .: "tree"
    
instance FromJSON ClientMessage where
  parseJSON = withObject "ClientMessage" $ \v ->
    CM
      <$> v .: "score"
      <*> v .: "a"
      <*> v .: "b"

instance ToJSON ClientTree where
    -- this generates a Value
    toJSON (CT tree grammar) =
      object ["tree" .= tree, "grammar" .= grammar]
    -- this encodes directly to a bytestring Builder
    toEncoding (CT tree grammar) =
      pairs ("tree" .= tree <> "grammar" .= grammar)

instance ToJSON ClientMessage where
    -- this generates a Value
    toJSON (CM score a b) =
      object ["score" .= score , "a" .= a , "b" .= b]
    -- this encodes directly to a bytestring Builder
    toEncoding (CM score a b) =
      pairs ("score" .= score <> "a" .= a <> "b" .= b)
      
--data CostTree = T { cost :: Int , lin :: String , tree :: String } deriving (Show)
data CostTree = T { cost :: Int , lin :: [(Path,String)] , tree :: String } deriving (Show)
-- lin is the full linearization

--data Menu = M (Map.Map (Int,Int) [[CostTree]]) deriving (Show)
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

instance FromJSON CostTree where
  parseJSON = withObject "CostTree" $ \v -> T
    <$> v .: "cost"
    <*> v .: "lin"
    <*> v .: "tree"

instance FromJSON Menu where
  parseJSON = withObject "CostTree" $ \v -> M
    <$> v .: "menu"
    
instance FromJSON ServerTree where
  parseJSON = withObject "ServerTree" $ \v -> ST
    <$> v .: "grammar"
    <*> v .: "tree"
    <*> v .: "lin"
    <*> v .: "menu"
    
instance FromJSON ServerMessage where
  parseJSON = withObject "ServerMessage" $ \v -> SM
    <$> v .: "success"
    <*> v .: "score"
    <*> v .: "a"
    <*> v .: "b"

instance ToJSON CostTree where
    -- this generates a Value
    toJSON (T score lin tree) =
      object ["score" .= score , "lin" .= lin , "tree" .= tree]
    -- this encodes directly to a bytestring Builder
    toEncoding (T score lin tree) =
      pairs ("score" .= score <> "lin" .= lin <> "tree" .= tree)

instance ToJSON Menu where
    toJSON (M map) =
      object [ (pack $ show k) .= (Map.!) map  k | k <- Map.keys map]
    toEncoding (M map) =
      if Data.List.null l then emptyObject_ else pairs $ Prelude.foldl (<>) (head l) (tail l) where l = [ (pack $ show k) .= (Map.!) map  k | k <- Map.keys map]

instance ToJSON ServerTree where
    -- this generates a Value
    toJSON (ST grammar tree lin menu) =
      object ["grammar" .= grammar , "tree" .= tree , "lin" .= lin , "menu" .= menu]
    -- this encodes directly to a bytestring Builder
    toEncoding (ST grammar tree lin menu) =
      pairs ("grammar" .= grammar <> "tree" .= tree <> "lin" .= lin <> "menu" .= menu)

instance ToJSON ServerMessage where
    -- this generates a Value
    toJSON (SM success score a b) =
      object ["success" .= success , "score" .= score , "a" .= a , "b" .= b]
    -- this encodes directly to a bytestring Builder
    toEncoding (SM success score a b) =
      pairs ("success" .= success <> "score" .= score <> "a" .= a <> "b" .= b)

data ClientMessageException = CME String deriving (Show)
data ReadTreeException = RTE String deriving (Show)

instance Exception ClientMessageException
instance Exception ReadTreeException

decodeClientMessage :: String -> ClientMessage
decodeClientMessage s =
  let rcm = eitherDecode (B.pack s) :: Either String ClientMessage
  in
    either (throw . CME) id rcm

encodeServerMessage :: ServerMessage -> String
encodeServerMessage sm =
  B.unpack $ encode sm

readTree :: Grammar -> String -> TTree
readTree grammar stree =
  maybe (throw (RTE $ "Error reading GF abstract syntax tree " ++ stree) :: TTree) (gfAbsTreeToTTreeWithGrammar grammar) (readExpr stree)

linearizeTree :: Grammar -> String -> String -> [(Path,String)]
linearizeTree grammar slang stree =
    let
      tree = readTree grammar stree
      toks = M.linearizeTree (grammar, mkCId slang) tree
   in
     toks

getMenus :: Context -> M.Precomputed -> String -> Menu
getMenus context prec stree =
  let
    tree = readTree (fst context) stree
    sug = suggestionFromPrecomputed context (prec ! (snd context)) tree
  in
    M $ Map.fromList $ map (\(c,t) -> (c,[t])) $ map (\(x,y) -> (x,map (\(a,b,c) -> T a b (showExpr [] $ ttreeToGFAbsTree c)) y)) sug -- list of lists -> list of menus

initPrecomputed :: Grammar -> IORef (Maybe Precomputed) -> String -> IO Precomputed
initPrecomputed grammar precRef body =
  let update =
        let cm = decodeClientMessage body
            langa = mkCId (cgrammar $ ca cm)
            langb = mkCId (cgrammar $ cb cm)
            treea = readTree grammar $ ctree $ ca cm
            treeb = readTree grammar $ ctree $ cb cm
            nprec = fromList [(langa,precomputeTrees (grammar,langa) treea), (langb,precomputeTrees (grammar,langb) treeb)]
        in
          do
            writeIORef precRef $ Just $ nprec
            return nprec
  in
    do
      prec <- readIORef precRef
      if isNothing prec then update
      else return $ fromJust prec
    
handleClientRequest :: Grammar -> Precomputed -> String -> IO String
handleClientRequest grammar prec body =
  do
    let cm = decodeClientMessage body
    -- Get new score
    let nscore = cscore cm + 1
    -- Check for Success
    let ctreea = ctree $ ca cm
    let ctreeb = ctree $ cb cm
    let nsuccess = ctreea == ctreeb
    -- Get new Suggestions
    let langa = (cgrammar $ ca cm)
    let langb = (cgrammar $ cb cm)
    let na = ST {
          sgrammar = langa, -- same language again
          stree = ctreea,
          slin = (linearizeTree grammar langa ctreea), -- linearization
          smenu = (getMenus (grammar, mkCId langa) prec ctreea) -- menus
          }
    let nb = ST {
          sgrammar = langb, -- same language again
          stree = ctreeb,
          slin = (linearizeTree grammar langb ctreeb), -- linearization linearizeTree ctreeb
          smenu = (getMenus (grammar, mkCId langb) prec ctreeb) -- menus
          }
    -- New ServerMessage
    let nsm = (SM nsuccess nscore na nb)
    putStrLn $ "\n\n" ++ (show nsm) ++ "#"
    return $ encodeServerMessage nsm
  
testMessage2 :: ServerMessage
testMessage2 =
  SM { ssuccess = False,
       sscore =  35,
       sa = tree,
       sb = tree
    }
  where
    tree = ST { sgrammar =  "MusteEng", stree =  "(StartUtt (UttS (UseCl ... (PredVP (...)) ...)))",
           slin = ["she", "doesn't", "break", "the", "yellow", "stones", "."],
           smenu = M $ Map.fromList
           [([0,0], [[ T {cost = 2, lin = [([0,0],"apples")] , tree = "(StartUtt ...)"},
                       T {cost = 2, lin = [([0,0],"x"),([0,1],"y"),([0,2],"z")], tree = "(StartUtt ...)"}]]),
            ([0,1],[[]])
            ]
           }

-- "{"success":false,"score":35,"a":{"grammar":"MusteEng","tree":"(StartUtt (UttS (UseCl ... (PredVP (...)) ...)))","lin":["she","doesn't","break","the","yellow","stones","."],"menu":{"4,4":[],"5,6":[{"score":2,"lin":"apples","tree":"(StartUtt ...)"},{"score":2,"lin":"x y z","tree":"(StartUtt ...)"}]}},"b":{"grammar":"MusteEng","tree":"(StartUtt (UttS (UseCl ... (PredVP (...)) ...)))","lin":["she","doesn't","break","the","yellow","stones","."],"menu":{"4,4":[],"5,6":[{"score":2,"lin":"apples","tree":"(StartUtt ...)"},{"score":2,"lin":"x y z","tree":"(StartUtt ...)"}]}}}"
