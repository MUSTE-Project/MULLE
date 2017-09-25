module Main where
import Network.Shed.Httpd
import Network.URI
import Data.List
import System.IO
import Ajax
import Muste
import Muste.Grammar
import PGF
import qualified Data.Map.Strict as Map
import qualified Data.ByteString.Char8 as B
import System.Environment
import Data.IORef
import Data.Maybe
import Data.Map
import Muste.Tree

filePath = "./demo"

getFileName :: String -> String
getFileName "/" = "muste.html"
getFileName ('/':fn) = fn

getType :: String -> String
getType fn
  | isSuffixOf "html" fn = "text/html"
  | isSuffixOf "css" fn = "text/css"
  | isSuffixOf "js" fn = "application/javascript"
  | isSuffixOf "ico" fn = "image/x-icon"
  | otherwise = "text/plain"

demoPrec :: Precomputed
demoPrec =
  let
    romanus_est_t = TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePron" (Fun "NP" ["Pron"]) [TNode "he_PP" (Fun "Pron" []) []],TNode "complA" (Fun "VP" ["A"]) [TNode "Romanus_A" (Fun "A" []) []]]]]
    laetus_est_t = TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePron" (Fun "NP" ["Pron"]) [TNode "he_PP" (Fun "Pron" []) []],TNode "complA" (Fun "VP" ["A"]) [TNode "laetus_A" (Fun "A" []) []]]]]
    augustus_romanus_est_t = TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePN" (Fun "NP" ["PN"]) [TNode "Augustus_PM" (Fun "PN" []) []],TNode "complA" (Fun "VP" ["A"]) [TNode "Romanus_A" (Fun "A" []) []]]]]
    augustus_laetus_est_t = TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePN" (Fun "NP" ["PN"]) [TNode "Augustus_PM" (Fun "PN" []) []],TNode "complA" (Fun "VP" ["A"]) [TNode "laetus_A" (Fun "A" []) []]]]]
    pse = [
      -- Romanus est
      ((romanus_est_t,[0,0,0,0]),
       [
       ]),
      ((romanus_est_t,[0,0,1]),
       [
       ]),
      ((romanus_est_t,[0,0]),
       [
       ]),
      ((romanus_est_t,[0]),
       [
       ]),
      ((romanus_est_t,[]),
       [
         (0,[([0,0,0,0],"he"),([0,0,1],"is"),([0,0,1,0],"happy")],laetus_est_t), -- Romanus est
         (0,[([0,0,0,0],"Augustus"),([0,0,1],"is"),([0,0,1,0],"Roman")],augustus_romanus_est_t), -- Augustus Romanus est
         (0,[([0,0,0,0],"Augustus"),([0,0,1],"is"),([0,0,1,0],"happy")],augustus_laetus_est_t) -- Augustus laetus est
       ]),
      ((romanus_est_t,[0,0,1,0]),
       [
         (0,[([0,0,0,0],"he"),([0,0,1],"is"),([0,0,1,0],"happy")],laetus_est_t)
       ]),
      ((romanus_est_t,[0,0,0]),
       [
         (0,[([0,0,0,0],"Augustus"),([0,0,1],"is"),([0,0,1,0],"Roman")],augustus_romanus_est_t)
       ]),
      -- laetus est
      ((laetus_est_t,[0,0,0,0]),
       [
       ]),
      ((laetus_est_t,[0,0,1]),
       [
       ]),
      ((laetus_est_t,[0,0]),
       [
       ]),
      ((laetus_est_t,[0]),
       [
       ]),
      ((laetus_est_t,[]),
       [
         (0,[([0,0,0,0],"he"),([0,0,1],"is"),([0,0,1,0],"Roman")],romanus_est_t), -- Romanus est
         (0,[([0,0,0,0],"Augustus"),([0,0,1],"is"),([0,0,1,0],"Roman")],augustus_romanus_est_t), -- Augustus Romanus est
         (0,[([0,0,0,0],"Augustus"),([0,0,1],"is"),([0,0,1,0],"happy")],augustus_laetus_est_t) -- Augustus laetus est
       ]),
      ((laetus_est_t,[0,0,1,0]),
       [
         (0,[([0,0,0,0],"he"),([0,0,1],"is"),([0,0,1,0],"Roman")],romanus_est_t)
       ]),
      ((laetus_est_t,[0,0,0]),
       [
         (0,[([0,0,0,0],"Augustus"),([0,0,1],"is"),([0,0,1,0],"happy")],augustus_laetus_est_t)
       ]),
      -- Augustus Romanus est
      ((augustus_romanus_est_t,[0,0,0,0]),
       [
       ]),
      ((augustus_romanus_est_t,[0,0,1]),
       [
       ]),
      ((augustus_romanus_est_t,[0,0]),
       [
       ]),
      ((augustus_romanus_est_t,[0]),
       [
       ]),
      ((augustus_romanus_est_t,[]),
       [
         (0,[([0,0,0,0],"he"),([0,0,1],"is"),([0,0,1,0],"Romanus")],romanus_est_t), -- Romanus est
         (0,[([0,0,0,0],"he"),([0,0,1],"is"),([0,0,1,0],"happy")],laetus_est_t), -- laetus est
         (0,[([0,0,0,0],"Augustus"),([0,0,1],"is"),([0,0,1,0],"Roman")],augustus_romanus_est_t), -- Augustus Romanus est
         (0,[([0,0,0,0],"Augustus"),([0,0,1],"is"),([0,0,1,0],"happy")],augustus_laetus_est_t) -- Augustus laetus est
       ]),
      ((augustus_romanus_est_t,[0,0,1,0]),
       [
         (0,[([0,0,0,0],"Augustus"),([0,0,1],"is"),([0,0,1,0],"happy")],augustus_laetus_est_t)
       ]),
      ((augustus_romanus_est_t,[0,0,0]),
       [
         (0,[([0,0,0,0],"he"),([0,0,1],"is"),([0,0,1,0],"Roman")],romanus_est_t)
       ]),
      -- Augustus laetus est
      ((augustus_laetus_est_t,[0,0,0,0]),
       [
       ]),
      ((augustus_laetus_est_t,[0,0,1]),
       [
       ]),
      ((augustus_laetus_est_t,[0,0]),
       [
       ]),
      ((augustus_laetus_est_t,[0]),
       [
       ]),
      ((augustus_laetus_est_t,[]),
       [
         (0,[([0,0,0,0],"he"),([0,0,1],"is"),([0,0,1,0],"Roman")],romanus_est_t), -- Romanus est
         (0,[([0,0,0,0],"he"),([0,0,1],"is"),([0,0,1,0],"happy")],laetus_est_t), -- laetus est
         (0,[([0,0,0,0],"Augustus"),([0,0,1],"is"),([0,0,1,0],"Roman")],augustus_romanus_est_t), -- Augustus Romanus est
         (0,[([0,0,0,0],"Augustus"),([0,0,1],"is"),([0,0,1,0],"happy")],augustus_laetus_est_t) -- Augustus laetus est
         ]),
      ((augustus_laetus_est_t,[0,0,1,0]),
       [
         (0,[([0,0,0,0],"Augustus"),([0,0,1],"is"),([0,0,1,0],"Roman")],augustus_romanus_est_t)
       ]),
      ((augustus_laetus_est_t,[0,0,0]),
       [
         (0,[([0,0,0,0],"he"),([0,0,1],"is"),([0,0,1,0],"happy")],laetus_est_t)
       ])
          ]
    psl = [
      -- Romanus est
      ((romanus_est_t,[0,0,0,0]),
       [
       ]),
      ((romanus_est_t,[0,0,1]),
       [
       ]),
      ((romanus_est_t,[0,0]),
       [
       ]),
      ((romanus_est_t,[0]),
       [
       ]),
      ((romanus_est_t,[]),
       [
         (0,[([0,0,0,0],""),([0,0,1,0],"laetus"),([0,0,1],"est")],laetus_est_t), -- Romanus est
         (0,[([0,0,0,0],"Augustus"),([0,0,1,0],"Romanus"),([0,0,1],"est")],augustus_romanus_est_t), -- Augustus Romanus est
         (0,[([0,0,0,0],"Augustus"),([0,0,1,0],"laetus"),([0,0,1],"est")],augustus_laetus_est_t) -- Augustus laetus est
       ]),
      ((romanus_est_t,[0,0,1,0]),
       [
         (0,[([0,0,0,0],""),([0,0,1,0],"laetus"),([0,0,1],"est")],laetus_est_t)
       ]),
      ((romanus_est_t,[0,0,0]),
       [
         (0,[([0,0,0,0],"Augustus"),([0,0,1,0],"Romanus"),([0,0,1],"est")],augustus_romanus_est_t)
       ]),
      -- laetus est
      ((laetus_est_t,[0,0,0,0]),
       [
       ]),
      ((laetus_est_t,[0,0,1]),
       [
       ]),
      ((laetus_est_t,[0,0]),
       [
       ]),
      ((laetus_est_t,[0]),
       [
       ]),
      ((laetus_est_t,[]),
       [
         (0,[([0,0,0,0],""),([0,0,1,0],"Romanus"),([0,0,1],"est")],romanus_est_t), -- Romanus est
         (0,[([0,0,0,0],"Augustus"),([0,0,1,0],"Romanus"),([0,0,1],"est")],augustus_romanus_est_t), -- Augustus Romanus est
         (0,[([0,0,0,0],"Augustus"),([0,0,1,0],"laetus"),([0,0,1],"est")],augustus_laetus_est_t) -- Augustus laetus est
       ]),
      ((laetus_est_t,[0,0,1,0]),
       [
         (0,[([0,0,0,0],""),([0,0,1,0],"Romanus"),([0,0,1],"est")],romanus_est_t)
       ]),
      ((laetus_est_t,[0,0,0]),
       [
         (0,[([0,0,0,0],"Augustus"),([0,0,1,0],"laetus"),([0,0,1],"est")],augustus_laetus_est_t)
       ]),
      -- Augustus Romanus est
      ((augustus_romanus_est_t,[0,0,0,0]),
       [
       ]),
      ((augustus_romanus_est_t,[0,0,1]),
       [
       ]),
      ((augustus_romanus_est_t,[0,0]),
       [
       ]),
      ((augustus_romanus_est_t,[0]),
       [
       ]),
      ((augustus_romanus_est_t,[]),
       [
         (0,[([0,0,0,0],""),([0,0,1,0],"Romanus"),([0,0,1],"est")],romanus_est_t), -- Romanus est
         (0,[([0,0,0,0],""),([0,0,1,0],"laetus"),([0,0,1],"est")],laetus_est_t), -- laetus est
         (0,[([0,0,0,0],"Augustus"),([0,0,1,0],"Romanus"),([0,0,1],"est")],augustus_romanus_est_t), -- Augustus Romanus est
         (0,[([0,0,0,0],"Augustus"),([0,0,1,0],"laetus"),([0,0,1],"est")],augustus_laetus_est_t) -- Augustus laetus est
       ]),
      ((augustus_romanus_est_t,[0,0,1,0]),
       [
         (0,[([0,0,0,0],"Augustus"),([0,0,1,0],"laetus"),([0,0,1],"est")],augustus_laetus_est_t)
       ]),
      ((augustus_romanus_est_t,[0,0,0]),
       [
         (0,[([0,0,0,0],""),([0,0,1,0],"Romanus"),([0,0,1],"est")],romanus_est_t)
       ]),
      -- Augustus laetus est
      ((augustus_laetus_est_t,[0,0,0,0]),
       [
       ]),
      ((augustus_laetus_est_t,[0,0,1]),
       [
       ]),
      ((augustus_laetus_est_t,[0,0]),
       [
       ]),
      ((augustus_laetus_est_t,[0]),
       [
       ]),
      ((augustus_laetus_est_t,[]),
       [
         (0,[([0,0,0,0],""),([0,0,1,0],"Romanus"),([0,0,1],"est")],romanus_est_t), -- Romanus est
         (0,[([0,0,0,0],""),([0,0,1,0],"laetus"),([0,0,1],"est")],laetus_est_t), -- laetus est
         (0,[([0,0,0,0],"Augustus"),([0,0,1,0],"Romanus"),([0,0,1],"est")],augustus_romanus_est_t), -- Augustus Romanus est
         (0,[([0,0,0,0],"Augustus"),([0,0,1,0],"laetus"),([0,0,1],"est")],augustus_laetus_est_t) -- Augustus laetus est
         ]),
      ((augustus_laetus_est_t,[0,0,1,0]),
       [
         (0,[([0,0,0,0],"Augustus"),([0,0,1,0],"Romanus"),([0,0,1],"est")],augustus_romanus_est_t)
       ]),
      ((augustus_laetus_est_t,[0,0,0]),
       [
         (0,[([0,0,0,0],""),([0,0,1,0],"laetus"),([0,0,1],"est")],laetus_est_t)
       ])
      ]
  in
    fromList [(mkCId "PrimaEng",pse), (mkCId "PrimaLat",psl)]

handleRequest :: Grammar -> IORef (Maybe Precomputed) -> Bool -> Request -> IO Response
handleRequest grammar prec isDemo request
  | isPrefixOf "/cgi"(uriPath $ reqURI request) =
      do
        putStrLn $ "CGI" ++ (show request)
        prec <- initPrecomputed grammar prec (reqBody request)
        result <- if isDemo then handleClientRequest grammar demoPrec (reqBody request)
                  else handleClientRequest grammar prec (reqBody request)
        return (Response 200 [("Content-type","application/json")] result)

  | otherwise = 
      do
        putStrLn $ "HTTP" ++ (show request)
        let file = getFileName $ uriPath $ reqURI request
        let typ = getType file
        content <- B.readFile $ filePath ++ "/" ++ file
        return (Response 200 [("Content-type",typ)] $ B.unpack content)

printHelp :: IO ()
printHelp =
  do
    putStrLn "Standalone backend for muste."
    putStrLn "  --demo: run in demo mode (i.e. hardcoded precomputations)"


main :: IO ()
main =
  do
    pgf <- readPGF "Grammar.pgf"
    let grammar = pgfToGrammar pgf
    args <- getArgs
    prec <- newIORef Nothing
    let isDemo = elem "--demo" args
    let isHelp = elem "--help" args
    if isHelp then printHelp
      else do { server <- initServer 8080 (handleRequest grammar prec isDemo) ; return () }
