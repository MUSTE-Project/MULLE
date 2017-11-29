module Protocol where

import Ajax
import Database


import Database.SQLite.Simple

import Muste hiding (linearizeTree)
import Muste.Grammar

-- -- | readTree reads a GF abstract syntax tree from a string and converts it to a TTree
-- readTree :: Grammar -> String -> TTree
-- readTree grammar stree =
--   maybe (throw (RTE $ "Error reading GF abstract syntax tree " ++ stree) :: TTree) (gfAbsTreeToTTree grammar) (readExpr stree)

-- -- | linearizeTree converts a GF abstract syntax tree from a string to a list of linearization tokens (i.e. tuples of path and string)
-- linearizeTree :: Grammar -> String -> String -> [(Path,String)]
-- linearizeTree grammar slang stree =
--     let
--       tree = readTree grammar stree
--       toks = M.linearizeTree (grammar, mkCId slang) tree
--    in
--      toks

-- -- | getMenus extract a menu from precomputed trees
-- getMenus :: Context -> M.Precomputed -> String -> Menu
-- getMenus context prec stree =
--   let
--     tree = readTree (fst context) stree :: TTree
--     sug = suggestionFromPrecomputed context (prec ! (snd context)) tree
--   in
--     M $ Map.fromList $ map (\(c,t) -> (c,[t])) $ map (\(x,y) -> (x,map (\(a,b,c) -> T a b (showExpr [] $ ttreeToGFAbsTree c)) y)) sug -- list of lists -> list of menus


-- initPrecomputed :: Grammar -> IORef (Maybe Precomputed) -> String -> IO Precomputed
-- initPrecomputed grammar precRef body =
--   let update =
--         let cm = decodeClientMessage body
--             langa = mkCId (cgrammar $ ca cm)
--             langb = mkCId (cgrammar $ cb cm)
--             treea = readTree grammar $ ctree $ ca cm
--             treeb = readTree grammar $ ctree $ cb cm
--             nprec = fromList [(langa,precomputeTrees (grammar,langa) treea), (langb,precomputeTrees (grammar,langb) treeb)]
--         in
--           do
--             writeIORef precRef $ Just $ nprec
--             return nprec
--   in
--     do
--       prec <- readIORef precRef
--       if isNothing prec then update
--       else return $ fromJust prec
    

-- handleClientRequest :: Grammar -> Precomputed -> String -> IO String
-- handleClientRequest grammar prec body =
--   do
--     let cm = decodeClientMessage body
--     -- Get new score
--     let nscore = cscore cm + 1
--     -- Check for Success
--     let ctreea = ctree $ ca cm
--     let ctreeb = ctree $ cb cm
--     let nsuccess = ctreea == ctreeb
--     -- Get new Suggestions
--     let langa = (cgrammar $ ca cm)
--     let langb = (cgrammar $ cb cm)
--     let na = ST {
--           sgrammar = langa, -- same language again
--           stree = ctreea,
--           slin = (linearizeTree grammar langa ctreea), -- linearization
--           smenu = (getMenus (grammar, mkCId langa) prec ctreea) -- menus
--           }
--     let nb = ST {
--           sgrammar = langb, -- same language again
--           stree = ctreeb,
--           slin = (linearizeTree grammar langb ctreeb), -- linearization linearizeTree ctreeb
--           smenu = (getMenus (grammar, mkCId langb) prec ctreeb) -- menus
--           }
--     -- New ServerMessage
-- --    let nsm = (SM nsuccess nscore na nb) -- TODO
--     let nsm = SMNull
--     let esm = encodeServerMessage nsm
--     putStrLn $ "\n\n" ++ (show esm) ++ "#"
--     return $ esm

handleClientRequest :: Connection -> Grammar -> Precomputed -> String -> IO String
handleClientRequest conn grammar prec body =
  do
    let cm = decodeClientMessage body
    case cm of {
      CMLoginRequest user pass -> handleLoginRequest user pass ;
      CMLessonsRequest token -> handleLessonsRequest token,
      CMLessonInit token lesson -> handleLessonInit token lesson
      }
  where
    handleLoginRequest :: String -> String -> IO String
    handleLoginRequest user pass =
      do
        authed <- authUser conn user pass
        token <- startSession conn user
        return $ encodeServerMessage $ if authed then do SMLoginSuccess token else SMLoginFail
    handleLessonsRequest :: String -> IO String
    handleLessonsRequest token =
      do
        verified <- verifySession conn token
        lessons <- listLessons conn token
        let lessonList = map (\(name,description,exercises,passed) -> Lesson name description exercises passed) lessons
        return $ encodeServerMessage $ tryVerified verified (SMLessonsList lessonList)
    handleLessonInit :: String -> String -> IO String
    handleLessonInit token lesson =
      do
        verified <- verifySession conn token
        startLesson conn token lesson
    tryVerified :: (Bool,String) -> ServerMessage -> ServerMessage
    tryVerified (True,_) m = m
    tryVerified (False,e) _ = (SMSessionInvalid e)
