{-# LANGUAGE DeriveDataTypeable, OverloadedStrings #-}

module Ajax where

import Data.Aeson
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
  slin :: [String] ,
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
      pairs $ Prelude.foldl (<>) (head l) (tail l) where l = [ (pack $ show k) .= (Map.!) map  k | k <- Map.keys map]

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

instance Exception ClientMessageException

decodeClientMessage :: String -> ClientMessage
decodeClientMessage s =
  let rcm = eitherDecode (B.pack s) :: Either String ClientMessage
  in
    either (throw . CME) id rcm

encodeServerMessage :: ServerMessage -> String
encodeServerMessage sm =
  B.unpack $ encode sm

linearizeTree :: Grammar -> String -> String -> [String]
linearizeTree grammar slang stree =
    let
      tree = gfAbsTreeToTTreeWithGrammar grammar $ fromJust $ readExpr stree -- !!!
      toks = M.linearizeTree (grammar, mkCId slang) tree
   in
     map snd toks

generateMenus :: Context -> String -> Menu
generateMenus context stree =
  let
    tree = gfAbsTreeToTTreeWithGrammar (fst context) $ fromJust $ readExpr stree -- !!!
    prec = precomputeTrees context tree
    -- sug = [((0,0),[(0,"Foo0",tree)]),((0,1),[(0,"Foo1",tree)]),((0,2),[(0,"Foo2",tree)]),((0,3),[(0,"Foo3",tree)]),
    --        ((1,0),[(0,"Bar0",tree)]),((1,1),[(0,"Bar1",tree)]),((1,2),[(0,"Bar2",tree)]),((1,3),[(0,"Bar3",tree)]),
    --        ((2,0),[(0,"Baz0",tree)]),((2,1),[(0,"Baz0",tree)]),((2,2),[(0,"Baz2",tree)]),((2,3),[(0,"Baz3",tree)])
    --       ]
    sug = suggestionFromPrecomputed context prec tree
--    foo = Map.fromList $ sug
  in
    M $ Map.fromList $ map (\(x,y) -> (x,map (\(a,b,c) -> [T a b (showExpr [] $ ttreeToGFAbsTree c)]) y)) sug -- list of lists ?!?

handleClientRequest :: Grammar -> String -> IO String
handleClientRequest grammar body =
  do
    let cm = decodeClientMessage body
    -- Get new Success
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
          smenu = (generateMenus (grammar, mkCId langa) ctreea) -- menus
          }
    let nb = ST {
          sgrammar = langb, -- same language again
          stree = ctreeb,
          slin = (linearizeTree grammar langb ctreeb), -- linearization linearizeTree ctreeb
          smenu = (generateMenus (grammar, mkCId langb) ctreeb) -- menus
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
