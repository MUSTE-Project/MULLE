module Ajax where

import Data.Aeson hiding (Null,String)
import qualified Data.Aeson as A
import Data.Aeson.Types hiding (Null)
import Data.Text (Text(..),pack,unpack)
import Data.Monoid
import Control.Exception
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.Map.Strict as Map
import Data.List
import Data.Maybe
import Muste hiding (linearizeTree)
import Muste.Grammar
import qualified Muste as M
import Muste.Tree
import PGF
import Data.Map hiding (map)
import Data.IORef

import qualified Data.Vector as V
import qualified Data.Text as T
data ClientTree = CT {
  cgrammar :: String,
  ctree :: String
  } deriving (Show) ;

createMessageObject :: String -> Value -> Value
createMessageObject msg params =
  object [
  T.pack "message" .= (A.String $ T.pack msg) ,
  T.pack "parameters" .= params
  ]
  
data ClientMessage = CMNull
                   | CMLoginRequest {
                       cusername :: String ,
                       cpassword :: String
                       }
                   | CMMOTDRequest { ctoken :: String }
                   | CMDataResponse {
                       ctoken :: String,
                       context :: String,
                       cdata :: [(String, String)]
                       }
                   | CMLessonsRequest { ctoken :: String }
                   | CMLessonInit {
                       ctoken :: String,
                       clesson :: String
                       }
                   | CMMenuRequest {
                       ctoken :: String,
                       cscore :: Int ,
                       ca :: ClientTree ,
                       cb :: ClientTree
                       }
                   deriving (Show) ;
  
instance FromJSON ClientTree where
  parseJSON = withObject "ClientTree" $ \v -> CT
    <$> v .: T.pack "grammar"
    <*> v .: T.pack "tree"
    
instance FromJSON ClientMessage where
  parseJSON =
    withObject "ClientMessage" $ \v ->
    do
      msg <- v .: T.pack "message" :: Parser Text
      params <- v .: T.pack "parameters" :: Parser Object
      case T.unpack $ msg of {
        "CMLoginRequest" ->
            CMLoginRequest
            <$> params .: T.pack "username"
            <*> params .: T.pack "password" ;
        "CMMOTDRequest" ->
            CMMOTDRequest
            <$> params .: T.pack "token" ;
        "CMDataResponse" ->
            (do
                ctoken <- params .: T.pack "token"
                ccontext <- params .: T.pack "context"
                cdata <- params .: T.pack "data"  :: Parser Value
                carray <- case cdata of {
                  Array a -> sequence $ V.toList $ V.map (withObject "Key-Value-Pair" $ \o -> do
                                                             f <- o .: T.pack "field"
                                                             v <- o .: T.pack "value"
                                                             return (f,v)
                                                         ) a ;
                    _ -> error "Boo, not an array"
                  }
                return $ CMDataResponse ctoken ccontext carray
            );
            -- (o .: T.pack "field", o .: T.pack "value")
        "CMLessonsRequest" -> 
            CMLessonsRequest
            <$> params .: T.pack "token" ;
        "CMLessonInit" -> 
            CMLessonInit
            <$> params .: T.pack "token"
            <*> params .: T.pack "lesson" ;
        "CMMenuRequest" -> 
            CMMenuRequest
             <$> params .: T.pack "token"
             <*> params .: T.pack "score"
             <*> params .: T.pack "a"
             <*> params .: T.pack "b"             
         }

instance ToJSON ClientTree where
    -- this generates a Value
    toJSON (CT tree grammar) =
      object [
      T.pack "tree" .= tree ,
      T.pack "grammar" .= grammar
      ]

instance ToJSON ClientMessage where
    -- this generates a Value
  toJSON (CMLoginRequest username password) =
    createMessageObject "CMLoginRequest" $ object [
    T.pack "username" .= username ,
    T.pack "password" .= password
    ]
  toJSON (CMMOTDRequest token) =
    createMessageObject "CMMOTDRequest" $ object [
    T.pack "token" .= token
    ]
  toJSON (CMDataResponse token context cdata) =
    createMessageObject "CMDataResponse" $ object [
    T.pack "token" .= token ,
    T.pack "context" .= context ,
    T.pack "data" .= map (\(k,v) -> object [ T.pack "field" .= k, T.pack "value" .= v ]) cdata
    ]
  toJSON (CMMenuRequest token score a b) =
    createMessageObject "CMMenuRequest" $ object [
    T.pack "token" .= token,
    T.pack "score" .= score ,
    T.pack "a" .= a ,
    T.pack "b" .= b
    ]

     
      
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

data ServerMessage = SMNull
                   | SMLoginSuccess { stoken :: String }
                   | SMLoginFail
                   | SMMOTDResponse { sfilename :: String }
                   | SMSessionInvalid { serror :: String }
                   | SMLessonsList { slessions :: [(String,Bool)] }
                   | SMMenuList {
                       ssuccess :: Bool ,
                       sscore :: Int ,
                       sa :: ServerTree ,
                       sb :: ServerTree
                       }
                   | SMLessonInvalid
                   | SMDataReceived
                   | SMDataInvalid { serror :: String }
                   deriving (Show) ;

instance FromJSON CostTree where
  parseJSON = withObject "CostTree" $ \v -> T
    <$> v .: T.pack "cost"
    <*> v .: T.pack "lin"
    <*> v .: T.pack "tree"

instance FromJSON Menu where
  parseJSON = withObject "CostTree" $ \v -> M
    <$> v .: T.pack "menu"
    
instance FromJSON ServerTree where
  parseJSON = withObject "ServerTree" $ \v -> ST
    <$> v .: T.pack "grammar"
    <*> v .: T.pack "tree"
    <*> v .: T.pack "lin"
    <*> v .: T.pack "menu"
    
instance FromJSON ServerMessage where
  parseJSON = withObject "ServerMessage" $ \v ->
    do
      msg <- v .: T.pack "message" :: Parser Text
      params <- v .:? T.pack "parameters" :: Parser (Maybe Object)
      case T.unpack $ msg of {
        "SMLoginSuccess" ->
            SMLoginSuccess <$> fromJust params .: T.pack "token" ;
        "SMLoginFail" -> return SMLoginFail ;
        "SMMOTDResponse" ->
            SMMOTDResponse <$> fromJust params .: T.pack "filename" ;
        "SMSessionInvalid" ->
            SMSessionInvalid <$> fromJust params .: T.pack "error" ;
        "SMLessonsList" ->
            (do
              cdata <- fromJust params .: T.pack "lessons"
              carray <- case cdata of {
                  Array a -> sequence $ V.toList $ V.map (withObject "Lesson-List" $ \o -> do
                                                             f <- o .: T.pack "name"
                                                             v <- o .: T.pack "passed"
                                                             return (f,v)
                                                         ) a ;
                    _ -> error "Boo, not an array"
                  }
              return $ SMLessonsList carray
            ) ;
        "SMMenuList" -> SMMenuList
            <$> fromJust params .: T.pack "success"
            <*> fromJust params .: T.pack "score"
            <*> fromJust params .: T.pack "a"
            <*> fromJust params .: T.pack "b" ;
        "SMLessonInvalid" -> return SMLessonInvalid ;
        "SMDataReceived" -> return SMDataReceived ;
        "SMDataInvalid" ->
            SMDataInvalid <$> fromJust params .: T.pack "error" ;
        }

instance ToJSON CostTree where
    -- this generates a Value
    toJSON (T score lin tree) =
      object [
      T.pack "score" .= score ,
      T.pack "lin" .= lin ,
      T.pack "tree" .= tree
      ]

instance ToJSON Menu where
    toJSON (M map) =
      object [ (pack $ show k) .= (Map.!) map  k | k <- Map.keys map]

instance ToJSON ServerTree where
    -- this generates a Value
    toJSON (ST grammar tree lin menu) =
      object [
      T.pack "grammar" .= grammar ,
      T.pack "tree" .= tree ,
      T.pack "lin" .= lin ,
      T.pack "menu" .= menu]



instance ToJSON ServerMessage where
    -- this generates a Value
  toJSON (SMLoginSuccess stoken) =
    createMessageObject "SMLoginSuccess" $ object [
    T.pack "token" .= (String $ T.pack stoken)
    ]
  toJSON SMLoginFail =
    createMessageObject "SMLoginFail" A.Null
  toJSON (SMMOTDResponse sfilename) =
    createMessageObject "SMMOTDRequest" $ object [
    T.pack "filename" .= (String $ T.pack sfilename)
    ]
  toJSON (SMSessionInvalid error) =
    createMessageObject "SMSessionInvalid" $ object [
    T.pack "error" .= (String $ T.pack error)
    ]
  toJSON (SMLessonsList slessons) =
    createMessageObject "SMLessonsList" $ object [
    T.pack "lessons" .= map (\(l,p) -> object [ T.pack "name" .= l, T.pack "passed" .= p]) slessons
    ]
  toJSON (SMMenuList ssuccess sscore sa sb) =
    createMessageObject "SMMenuList" $ object [
    T.pack "success" .= ssuccess ,
    T.pack "score" .= sscore ,
    T.pack "a" .= sa ,
    T.pack "b" .= sb
    ]
  toJSON SMLessonInvalid =
    createMessageObject "SMLessonInvalid" A.Null
  toJSON SMDataReceived =
    createMessageObject "SMDataReceived" A.Null
  toJSON (SMDataInvalid error) =
    createMessageObject "SMDataInvalid" $ object [
    T.pack "error" .= (String $ T.pack error)
    ]
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

-- | readTree reads a GF abstract syntax tree from a string and converts it to a TTree
readTree :: Grammar -> String -> TTree
readTree grammar stree =
  maybe (throw (RTE $ "Error reading GF abstract syntax tree " ++ stree) :: TTree) (gfAbsTreeToTTree grammar) (readExpr stree)

-- | linearizeTree converts a GF abstract syntax tree from a string to a list of linearization tokens (i.e. tuples of path and string)
linearizeTree :: Grammar -> String -> String -> [(Path,String)]
linearizeTree grammar slang stree =
    let
      tree = readTree grammar stree
      toks = M.linearizeTree (grammar, mkCId slang) tree
   in
     toks

-- | getMenus extract a menu from precomputed trees
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
--    let nsm = (SM nsuccess nscore na nb) -- TODO
    let nsm = SMNull
    let esm = encodeServerMessage nsm
    putStrLn $ "\n\n" ++ (show esm) ++ "#"
    return $ esm
