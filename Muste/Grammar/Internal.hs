{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{- | This Module is the internal implementation behind the module 'Muste.Grammar' -}
module Muste.Grammar.Internal where
import PGF hiding (parse)
import PGF.Internal hiding (nub)
import Data.Maybe
import Data.Set (Set(..),fromList)
import Test.QuickCheck
import Text.Parsec
import Data.Char
import Data.List

wildCard = "*empty*"

-- | Type 'FunType' consists of a String that is the the result category and [String] are the parameter categories
data FunType = Fun String [String] | NoType deriving (Ord,Eq,Show,Read)

-- | A 'FunType' is in the Show class
-- instance Show FunType where
--   show (Fun cat []) =
--     "(" ++ show cat ++ ")"
--   show (Fun cat cats) =
--     "(" ++ (foldl (\a b -> a ++ " -> " ++ show b) (show $ head cats) (tail cats) ++ " -> " ++ show cat) ++ ")"
--   show NoType = "()"

-- | Monadic parser combinator to read a 'FunType'
-- parsecFunType :: Stream s m Char => ParsecT s u m FunType
-- parsecFunType =
--   let
--     bracketed :: Stream s m Char => ParsecT s u m [CId]
--     bracketed = do { char '(' ; spaces ; fs <- many (do { i <- id ; f <- many fun; return (i:concat f)} ); spaces ; char ')' ; return $ concat fs }
--     id :: Stream s m Char => ParsecT s u m CId
--     id = do { i <- many1 $ noneOf "(->) "; return $ mkCId i }
--     fun :: Stream s m Char => ParsecT s u m [CId]
--     fun = do { spaces ; string "->" ; spaces ; i <- id ; spaces ; return [i] }
--   in
--     do
--       spaces
--       cids <- (bracketed <|> fmap (: []) id)
--       case cids of {
--         [] -> return NoType ; 
--         _ -> return (Fun (last cids) (init cids)) 
--         }

-- parsecPlusRest :: Stream s m Char => ParsecT s u m a -> ParsecT s u m (a,String)
-- parsecPlusRest parser =
--   do
--     elem <- parser
--     rest <- many anyChar
--     return (elem,rest)

-- | A 'FunType' is in the Read class
-- instance Read FunType where
--   readsPrec _ sType =
--     let
--       result = parse (parsecPlusRest parsecFunType) "read" sType 
--     in
--       case result of {
--         Left e -> error $ show e ;
--         Right (fun,rest) -> [(fun,rest)]
--         }

-- A 'FunType' can be generated randomly
instance Arbitrary FunType where
  arbitrary =
    frequency [(9,sized newFun),(1,return NoType)]
    where
      newFun len = do
        let ids = ['A'..'E']
        cat <- elements ids
        cats <- resize len $ listOf1 $ elements ids
        return $ Fun [cat] (map charToString cats)
      charToString c = [c]

-- | Type 'Rule' consists of a String as the function name and a 'FunType' as the Type
data Rule = Function String FunType deriving (Ord,Eq,Show,Read)

-- | A 'Rule' is member of the Show class
-- instance Show Rule where
--   show (Function name funtype) =
--     show name ++ " : " ++ show funtype ;

-- | Monadic parser combinator to read a 'Rule'
-- parsecRule :: Stream s m Char => ParsecT s u m (Rule,String)
-- parsecRule =
--   let
--     id :: Stream s m Char => ParsecT s u m String
--     id = many $ noneOf ": "
--   in
--     do
--       i <- id
--       spaces
--       char ':'
--       spaces
--       (ft,rest) <- parsecPlusRest parsecFunType
--       return (Function (mkCId i) ft,rest)

-- | A 'FunType' is in the Read class
-- instance Read Rule where
--   readsPrec _ sType =
--     let
--       result = parse parsecRule "read" sType
--     in
--       case result of {
--         Left e -> error $ show e ;
--         Right (rule,rest) -> [(rule,rest)]
--         }

-- A 'FunType' can be generated randomly
instance Arbitrary Rule where
  arbitrary =
    do
      let ids = ['f'..'z']
      id <- elements ids
      funtype <- arbitrary 
      return $ Function [id] funtype
      
-- | Type 'Grammar' consists of a start categorie and a list of rules
data Grammar = Grammar {
  startcat :: String,
  synrules :: [Rule],
  lexrules :: [Rule],
  pgf :: PGF
  }

instance Arbitrary Grammar where
  arbitrary =
    do
      -- generate list of rules
      genrules <- fmap (filter (\f -> case f of { (Function _ NoType) -> False ; _ -> True })) $ listOf1 (resize 3 arbitrary)
      let filterrules = nubBy (\(Function id1 _) (Function id2 _) -> id1 == id2 ) genrules
      let rules = if not $ null filterrules then filterrules else [(Function "f" (Fun "A" ["A"]))]
      -- select start category
      let startCat = getRuleCat $ head rules
      -- get all the cats on the rhss
      let allCats = nub $ concat $ map (\(Function _ (Fun _ cats)) -> cats) rules -- Problematic
      let lexRules = map (\c -> Function (map toLower c) (Fun c [])) allCats
      return $ Grammar startCat rules lexRules emptyPGF
      
-- | A 'Grammar' is in the EQ class
instance Eq Grammar where
  (==) g1@(Grammar s1 rs1 ls1 pgf1) g2@(Grammar s2 rs2 ls2 pgf2) =
    s1 == s2 &&
    rs1 == rs2 &&
    ls1 == ls2
    -- pgf1 == pgf2 -- To be fixed somehow
    
-- | A 'Grammar' is in the Show class
instance Show Grammar where
  show (Grammar startcat srules lrules _) =
    "Startcat: " ++ show startcat ++ "\nSyntactic Rules: \n" ++
    unwords (map (\r -> "\t" ++ show r ++ "\n") srules)
    ++ "\nLexical Rules: \n" ++
    unwords (map (\r -> "\t" ++ show r ++ "\n") lrules)

-- | Constant for an empty 'Grammar' in line with 'emptyPGF'
emptyGrammar = Grammar wildCard [] [] emptyPGF

-- | Predicate to check if a PGF is empty, i.e. when the absname is wildCId
isEmptyPGF pgf = absname pgf == wildCId

-- | Predicate to check if a Grammar is empty, i.e. when the startcat is wildCId and pgf is empty
isEmptyGrammar grammar = startcat grammar == wildCard && isEmptyPGF (pgf grammar)

prop_grammarLexRulesNotEmpty :: Grammar -> Property
prop_grammarLexRulesNotEmpty g = property $ not $ null $ lexrules g

prop_grammarSynRulesNotEmpty :: Grammar -> Property
prop_grammarSynRulesNotEmpty g = property $ not $ null $ synrules g

prop_grammarHasRulesForAllCats :: Grammar -> Property
prop_grammarHasRulesForAllCats g =
  let
    test c =
      property $ not $ null $ getRulesList (synrules g ++ lexrules g) [c]
    cats = nub $ concat $ map (\(Function _ (Fun c cs)) -> c:cs) $ (synrules g ++ lexrules g)
  in
    (not $ isEmptyGrammar g) ==> conjoin (map test cats)
  
  
-- | The function 'readId' is a helper to read a 'FunType'
readId :: String -> Maybe (CId,String)
-- Workaround for ? (used for unknown types)
readId ('?':rest) =
  let
    tmp = readId rest
  in
    case tmp of {
      Nothing -> Just (mkCId "?","") ;
      Just (id,rst) -> Just (mkCId  ("?" ++ show id),rst)
      }
readId str =
  let
    result = reads str
  in
    if null result then Nothing else Just $ head result


-- | The function 'getFunType' extracts the function type from a grammar given a function name
getFunType :: PGF -> CId -> FunType
getFunType grammar id
  | isEmptyPGF grammar = NoType -- Empty grammar
  | otherwise =
    let
      typ = functionType grammar id
    in
      case typ of {
        Nothing -> NoType ; -- No type found in grammar
        Just t ->
        let
          (hypos,typeid,exprs) = unType t
          cats = map (\(_,_,DTyp _ cat _) -> cat) hypos
        in
          Fun (showCId typeid) (map showCId cats)
        }
      
getFunType2 :: Grammar -> String -> FunType
getFunType2 g id =
  let
    rules = filter (\r -> getRuleName r == id) $ getAllRules g
  in
    if not $ null rules then getRuleType $ head rules else NoType

prop_funTypeEquality :: PGF -> Property
prop_funTypeEquality pgf =
  let
    grammar = pgfToGrammar pgf
    funs = functions pgf
  in
    property $ and $ map (\f -> getFunType pgf f == getFunType2 grammar (showCId f)) funs

-- | The function 'getFunCat' extracts the result category from a function type
getFunCat :: FunType -> String
getFunCat (Fun cat _) = cat
getFunCat _ = wildCard

-- | The function 'getRuleCat' extracts the result category of a rule
getRuleCat :: Rule -> String
getRuleCat (Function _ funType) = getFunCat funType

-- | The function 'getRuleName' extracts the name of a rule
getRuleName :: Rule -> String
getRuleName (Function name _) = name

-- | The function 'getRuleType' extracts the full type of a rule
getRuleType :: Rule -> FunType
getRuleType (Function _ funType) = funType

-- | The function 'getRules' finds all rules in grammar that have a certain result category
getRulesSet :: [Rule] -> [String] -> Set Rule
getRulesSet rules cats =
  -- Convert rules from GF format to our only one
  fromList $ concatMap (\c -> filter (\(Function _ (Fun fcat _)) -> fcat == c ) rules) cats

-- | The function 'getRules' finds all rules in grammar that have a certain result category
getRulesList :: [Rule] -> [String] -> [Rule]
getRulesList rules cats =
  -- Convert rules from GF format to our only one
  concatMap (\c -> filter (\(Function _ (Fun fcat _)) -> fcat == c ) rules) cats

-- | The function 'getRules' returns the union of syntactic and lexical rules of a grammar
getAllRules :: Grammar -> [Rule]
getAllRules g = union (synrules g) (lexrules g)

-- | The function 'pgfToGrammar' transforms a PGF grammar to a simpler grammar data structure
pgfToGrammar :: PGF -> Grammar
pgfToGrammar pgf 
  | isEmptyPGF pgf = emptyGrammar
  | otherwise =
    let
      -- Get function names
      funs = functions pgf
      -- Get their types
      funtypes = map (getFunType pgf) funs
      -- Combine to a rule
      rules = zipWith Function (map showCId funs) funtypes
      -- Split in lexical and syntactical rules
      (lexrules,synrules) = partition (\r -> case r of { Function _ (Fun _ []) -> True ; _ -> False } ) rules
      -- Get the startcat from the PGF
      (_, startcat, _) = unType (startCat pgf)
    in
      Grammar (showCId startcat) synrules lexrules pgf


