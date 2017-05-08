{- | Implements several tests to control the validy of the program
-}
module Test.Grammar where
import Test.QuickCheck
import Test.Framework
import PGF
import PGF.Internal
import Muste.Grammar.Internal
import Test.HUnit.Text
import Test.HUnit.Base
import Data.Maybe
import qualified Data.Map as M
import Control.Monad
import Data.Set (Set(..),empty,fromList)
import Data.List (sort,nub)

-- HUnit tests
hunit_Eq_Grammar_eq_test =
  let
    grammar1 = Grammar "S"
      [
        Function "f" (Fun "A" ["A","B"]),
        Function "g" (Fun "B" ["B","C"]),
        Function "h" (Fun "A" ["A","A","A"]),
        Function "s" (Fun "S" ["A"])
      ]
      [
        Function "a" (Fun "A" []),
        Function "b" (Fun "B" []),
        Function "c" (Fun "C" [])
      ]
      emptyPGF
    grammar2 = Grammar "A" [] [] emptyPGF
    pgf = readPGF "gf/ABCAbs.pgf"
    grammar3 = fmap pgfToGrammar pgf
  in
    TestList [
    TestLabel "Empty grammar" ( emptyGrammar == emptyGrammar ~?= True ),
    TestLabel "Simple Grammar reflexivity" ( grammar1 == grammar1 ~?= True ),
    TestLabel "Inequality 1" ( grammar1 == grammar2 ~?= False ),
    TestLabel "Inequality 2" ( grammar2 == grammar1 ~?= False ),
    TestLabel "Complex grammar" $ TestCase $ join $ fmap (\g -> grammar1 == g @?= True) grammar3
    ]
    
hunit_Show_FunType_show_test =
  let
    type1 = NoType
    type2 = Fun "A" []
    type3 = Fun "A" ["A"]
    type4 = Fun "A" ["A","B"]
  in
    TestList [
    TestLabel "No Type" ( show type1 ~?= "NoType" ),
    TestLabel "Simple Type" ( show type2 ~?= "Fun \"A\" []" ),
    TestLabel "Function Type 1" ( show type3 ~?= "Fun \"A\" [\"A\"]" ),
    TestLabel "Function Type 2" ( show type4 ~?= "Fun \"A\" [\"A\",\"B\"]" )
    ]

hunit_Show_Rule_show_test =
  let
    fun1 = Function "f1" NoType
    fun2 = Function "f2" (Fun "A" [])
    fun3 = Function "f3" (Fun "A" ["A","B"])
  in
    TestList [
    TestLabel "No Type" ( show fun1 ~?= "Function \"f1\" NoType" ),
    TestLabel "Simple Type" ( show fun2 ~?= "Function \"f2\" (Fun \"A\" [])" ),
    TestLabel "Function Type" ( show fun3 ~?= "Function \"f3\" (Fun \"A\" [\"A\",\"B\"])" )
    ]

hunit_Show_Grammar_show_test =
  let
    grammar1 = Grammar "S" [] [] emptyPGF
    grammar2 = Grammar "S"
      []
      [
        Function "a" (Fun "A" []),
        Function "b" (Fun "B" [])
      ]
      emptyPGF
    grammar3 = Grammar "S"
      [
        Function "f1" (Fun "A" ["A","B"]),
        Function "f2" (Fun "B" ["B","B"])
      ]
      []
      emptyPGF
    grammar4 = Grammar "S"
      [
        Function "f1" (Fun "A" ["A","B"]),
        Function "f2" (Fun "B" ["B","B"])
      ]
      [
        Function "a" (Fun "A" []),
        Function "b" (Fun "B" [])
      ]
      emptyPGF
  in
    TestList [
    TestLabel "Empty Grammar" ( show grammar1 ~?= "Startcat: \"S\"\nSyntactic Rules: \n\nLexical Rules: \n" ),
    TestLabel "Simple Grammar 1" ( show grammar2 ~?= "Startcat: \"S\"\nSyntactic Rules: \n\nLexical Rules: \n\tFunction \"a\" (Fun \"A\" [])\n \tFunction \"b\" (Fun \"B\" [])\n" ),
    TestLabel "Simple Grammar 2" ( show grammar3 ~?= "Startcat: \"S\"\nSyntactic Rules: \n\tFunction \"f1\" (Fun \"A\" [\"A\",\"B\"])\n \tFunction \"f2\" (Fun \"B\" [\"B\",\"B\"])\n\nLexical Rules: \n" ),
    TestLabel "Grammar" ( show grammar4 ~?= "Startcat: \"S\"\nSyntactic Rules: \n\tFunction \"f1\" (Fun \"A\" [\"A\",\"B\"])\n \tFunction \"f2\" (Fun \"B\" [\"B\",\"B\"])\n\nLexical Rules: \n\tFunction \"a\" (Fun \"A\" [])\n \tFunction \"b\" (Fun \"B\" [])\n" )
    ]

hunit_Read_FunType_read_test =
  let
    str1 = "NoType"
    type1 = NoType
    str2 = "Fun \"A\" []"
    type2 = Fun "A" []
    str3 = "Fun \"B\" [\"A\"]"
    type3 = Fun "B" ["A"]
    str4 = "Fun \"C\" [\"A\",\"B\"]"
    type4 = Fun "C" ["A","B"]
  in
    TestList [
    TestLabel "No Type" ( read str1 ~?= type1 ),
    TestLabel "Simple Type" ( read str2 ~?= type2 ),
    TestLabel "Function Type 1" ( read str3 ~?= type3 ),
    TestLabel "Function Type 2" ( read str4 ~?= type4 )
    ]

hunit_Read_Rule_read_test =
  let
    str1 = "Function \"f\" NoType"
    type1 = Function "f" NoType
    str2 = "Function \"f\" (Fun \"A\" [])"
    type2 = Function "f" (Fun "A" [])
    str3 = "Function \"f\" (Fun \"B\" [\"A\"])"
    type3 = Function "f" (Fun "B" ["A"])
    str4 = "Function \"f\" (Fun \"C\" [\"A\",\"B\"])"
    type4 = Function "f" (Fun "C" ["A","B"])
  in
    TestList [
    TestLabel "No Type" ( read str1 ~?= type1 ),
    TestLabel "Simple Type" ( read str2 ~?= type2 ),
    TestLabel "Function Type 1" ( read str3 ~?= type3 ),
    TestLabel "Function Type 2" ( read str4 ~?= type4 )
    ]


hunit_isEmptyPGF_test =
  let
    pgf = PGF M.empty (mkCId "Abs") (Abstr M.empty M.empty M.empty) M.empty
    pgf2 = readPGF "gf/ABCAbs.pgf"
  in
  TestList [
  TestLabel "Empty PGF" $ isEmptyPGF emptyPGF ~?= True,
  TestLabel "Almost empty PGF with a name" $ isEmptyPGF pgf ~?= False,
  TestLabel "Non-empty PGF" $ TestCase $ pgf2 >>= (\g -> isEmptyPGF g @?= False)
  ]

hunit_isEmptyGrammar_test =
  let
    grammar1 = Grammar "S"
      [
        Function "f" (Fun "S" ["A"]),
        Function "a" (Fun "A" [])
      ]
      []
      emptyPGF
    pgf = readPGF "gf/ABCAbs.pgf"
    grammar2 = fmap (Grammar wildCard [] []) pgf
  in
    TestList [
    TestLabel "Empty Grammar" (isEmptyGrammar emptyGrammar ~?= True),
    TestLabel "Almost empty Grammar with a name" (isEmptyGrammar grammar1 ~?= False),
    TestLabel "Grammar without a name" $ TestCase $ grammar2 >>= (\g -> isEmptyGrammar g @?= False),
    TestLabel "Complete grammar from PGF" $ TestCase $ pgf >>= (\g -> isEmptyGrammar (pgfToGrammar g) @?= False)
    ]
  
hunit_getFunTypeWithPGF_test =
hunit_readId_test =
  let
    pgf = readPGF "gf/ABCAbs.pgf"
    str1 = " "
    str2 = "_"
    str3 = "?"
    str4 = "A"
    str5 = " A"
    str6 = "_A"
    str7 = "?A"
    str8 = "??"
    str9 = "ABC"
    str10 = "Abc"
    str11 = "A_B_C"
    str12 = "A.B.C"
    str13 = "A?"
  in
    TestList [
    TestLabel "Empty PGF" $ getFunTypeWithPGF emptyPGF (mkCId "f") ~?= NoType,
    TestLabel "Existing Constant" $ TestCase $ pgf >>= (\g -> getFunTypeWithPGF g (mkCId "a") @?= Fun "A" [] ),
    TestLabel "Existing Function" $ TestCase $ pgf >>= (\g -> getFunTypeWithPGF g (mkCId "f") @?= Fun "A" ["A", "B"]),
    TestLabel "Non-Existing Function" $ TestCase $ pgf >>= (\g -> getFunTypeWithPGF g (mkCId "foo") @?= NoType)
    TestLabel "Unacceptable Letter 1" ( readId str1 ~?= Nothing ),
    TestLabel "Unacceptable Letter 2" ( readId str2 ~?= Nothing ),
    TestLabel "Unacceptable Letter 3" ( readId str3 ~?= Just (mkCId "?","") ),
    TestLabel "Single Letter 1" ( readId str4 ~?= Just (mkCId "A","") ),
    TestLabel "Single Letter 2" ( readId str5 ~?= Nothing ),
    TestLabel "Multiple Letters 1" ( readId str6 ~?= Just (mkCId "_A","") ),
    TestLabel "Multiple Letters 2" ( readId str7 ~?= Just (mkCId "?A","") ),
    TestLabel "Multiple Letters 3" ( readId str8 ~?= Just (mkCId "?\'?\'","") ),
    TestLabel "Multiple Letters 4" ( readId str9 ~?= Just (mkCId "ABC","") ),
    TestLabel "Multiple Letters 5" ( readId str10 ~?= Just (mkCId "Abc","") ),
    TestLabel "Multiple Letters 6" ( readId str11 ~?= Just (mkCId "A_B_C","") ),
    TestLabel "Multiple Letters 7" ( readId str12 ~?= Just (mkCId "A",".B.C") ),
    TestLabel "Multiple Letters 8" ( readId str13 ~?= Just (mkCId "A","?") ),
    TestLabel "Single Letter with rest 1" ( readId (str4 ++ "###") ~?= Just (mkCId "A","###") ),
    TestLabel "Single Letter with rest 2" ( readId (str4 ++ " ###") ~?= Just (mkCId "A"," ###") ),
    TestLabel "Single Letter with rest 1" ( readId (str9 ++ "###") ~?= Just (mkCId "ABC","###") ),
    TestLabel "Single Letter with rest 2" ( readId (str9 ++ " ###") ~?= Just (mkCId "ABC"," ###") )
    ]

    
hunit_getFunTypeWithGrammar_test =
  let
    pgf = readPGF "gf/ABCAbs.pgf"
    grammar = fmap pgfToGrammar pgf
  in
    TestList [
    TestLabel "Empty PGF" $ getFunTypeWithGrammar emptyGrammar "f" ~?= NoType,
    TestLabel "Existing Constant" $ TestCase $ grammar >>= (\g -> getFunTypeWithGrammar g "a" @?= Fun "A" [] ),
    TestLabel "Existing Function" $ TestCase $ grammar >>= (\g -> getFunTypeWithGrammar g "f" @?= Fun "A" ["A", "B"]),
    TestLabel "Non-Existing Function" $ TestCase $ grammar >>= (\g -> getFunTypeWithGrammar g "foo" @?= NoType)
    ]

hunit_getFunCat_test =
  TestList [
  TestLabel "NoType" ( getFunCat NoType ~?= wildCard),
  TestLabel "Constant" ( getFunCat (Fun "A" []) ~?= "A"),
  TestLabel "Constant" ( getFunCat (Fun "A" ["A","B"]) ~?= "A")
  ]

hunit_getRuleCat_test =
  TestList [
  TestLabel "NoType" ( getRuleCat (Function "f" NoType) ~?= wildCard),
  TestLabel "Constant" ( getRuleCat (Function "f" (Fun "A" [])) ~?= "A"),
  TestLabel "Constant" ( getRuleCat (Function "f" (Fun "A" ["A","B"])) ~?= "A")
  ]

hunit_getRuleName_test =
  TestList [
  TestLabel "NoType" ( getRuleName (Function "f" NoType) ~?= "f"),
  TestLabel "Constant" ( getRuleName (Function "g" (Fun "A" [])) ~?= "g"),
  TestLabel "Constant" ( getRuleName (Function "h" (Fun "A" ["A","B"])) ~?= "h")
  ]
  
hunit_getRulesSet_test =
  let
    rule1 = Function "r1" (Fun "A" [])
    rule2 = Function "r2" (Fun "A" ["A"])
    rule3 = Function "r3" (Fun "B" ["A"])
    rule4 = Function "r4" (Fun "A" ["A","A"])
    grammar = Grammar "S"
      [ rule2, rule3, rule4 ]
      [ rule1 ]
      emptyPGF
  in
    TestList [
    TestLabel "Empty Grammar" ( getRulesSet (getAllRules emptyGrammar) [] ~?= empty),
    TestLabel "No categories" ( getRulesSet (getAllRules grammar) [] ~?= empty),
    TestLabel "No match" ( getRulesSet (getAllRules grammar) ["Z"] ~?= empty),
    TestLabel "One match" ( getRulesSet (getAllRules grammar) ["B"] ~?= fromList [rule3]),
    TestLabel "Three matches" ( getRulesSet (getAllRules grammar) ["A"] ~?= fromList [rule1, rule2, rule4]),
    TestLabel "All matches" ( getRulesSet (getAllRules grammar) ["A","B"] ~?= fromList (getAllRules grammar))
    ]

hunit_getRulesList_test =
  let
    rule1 = Function "r1" (Fun "A" [])
    rule2 = Function "r2" (Fun "A" ["A"])
    rule3 = Function "r3" (Fun "B" ["A"])
    rule4 = Function "r4" (Fun "A" ["A","A"])
    grammar = Grammar "S"
      [ rule2, rule3, rule4 ]
      [ rule1 ]
      emptyPGF
  in
    TestList [
    TestLabel "Empty Grammar" ( getRulesList (getAllRules emptyGrammar) [] ~?= []),
    TestLabel "No categories" ( getRulesList (getAllRules grammar) [] ~?= []),
    TestLabel "No match" ( getRulesList (getAllRules grammar) ["Z"] ~?= []),
    TestLabel "One match" ( getRulesList (getAllRules grammar) ["B"] ~?= [rule3]),
    TestLabel "Three matches" ( getRulesList (getAllRules grammar) ["A"] ~?= [rule2, rule4, rule1]),
    TestLabel "All matches" ( ( sort $ getRulesList (getAllRules grammar) ["A","B"]) ~?= (sort $ getAllRules grammar))
    ]

hunit_getAllRules_test =
  let
    rule1 = Function "r1" (Fun "A" [])
    rule2 = Function "r2" (Fun "B" [])
    rule3 = Function "r3" (Fun "A" ["A","A"])
    rule4 = Function "r4" (Fun "A" ["B","A"])
    grammar1 = Grammar "S" [] [] emptyPGF
    grammar2 = Grammar "S" [ rule3, rule4] [] emptyPGF
    grammar3 = Grammar "S" [] [ rule1, rule2 ] emptyPGF
    grammar4 = Grammar "S" [ rule3, rule4] [ rule1, rule2 ] emptyPGF
  in
    TestList [
    TestLabel "Empty Grammar 1" ( (getAllRules emptyGrammar) ~?= []),
    TestLabel "Empty Grammar 2" ( (getAllRules grammar1) ~?= []),
    TestLabel "Partial Grammar 1" ( (getAllRules grammar2) ~?= [rule3,rule4]),
    TestLabel "Partial Grammar 2" ( (getAllRules grammar3) ~?= [rule1,rule2]),
    TestLabel "Full Grammar 1" ( (getAllRules grammar4) ~?= [rule3,rule4,rule1,rule2])
    ]
    
hunit_pgfToGrammar_test =
  let
    pgf = readPGF "gf/ABCAbs.pgf"
    grammar = fmap (Grammar
                    "S"
                    [
                      Function "f" (Fun "A" ["A","B"]),
                      Function "g" (Fun "B" ["B","C"]),
                      Function "h" (Fun "A" ["A","A","A"]),
                      Function "s" (Fun "S" ["A"])
                    ]
                    [
                      Function "a" (Fun "A" []),
                      Function "b" (Fun "B" []),
                      Function "c" (Fun "C" [])
                    ]
                   ) pgf
  in
    TestList [
    TestLabel "Non-empty PGF" $ TestCase $ join $ liftM2 (@?=) (fmap pgfToGrammar pgf ) grammar
    ]

eq_tests = TestList [
  TestLabel "Eq Grammar ===" hunit_Eq_Grammar_eq_test
  ]

show_tests = TestList [
  TestLabel "Show FunType show" hunit_Show_FunType_show_test,
  TestLabel "Show Rule show" hunit_Show_Rule_show_test,
  TestLabel "Show Grammar show" hunit_Show_Grammar_show_test
  ]

read_tests = TestList [
  TestLabel "Read FunType read" hunit_Read_FunType_read_test,
  TestLabel "Read Rule read" hunit_Read_Rule_read_test
  ]

grammar_function_tests =
  TestList [
  TestLabel "isEmptyPGF" hunit_isEmptyPGF_test,
  TestLabel "isEmptyGrammar" hunit_isEmptyGrammar_test,
  TestLabel "readId" hunit_readId_test,
  TestLabel "getFunTypeWithPGF" hunit_getFunTypeWithPGF_test,
  TestLabel "getFunTypeWithPGF" hunit_getFunTypeWithGrammar_test,
  TestLabel "getFunCat" hunit_getFunCat_test,
  TestLabel "getRuleCat" hunit_getRuleCat_test,
  TestLabel "getRuleName" hunit_getRuleName_test,
  TestLabel "getRulesSet" hunit_getRulesSet_test,
  TestLabel "getRulesList" hunit_getRulesList_test,
  TestLabel "getAllRules" hunit_getAllRules_test,
  TestLabel "pgfToGrammar" hunit_pgfToGrammar_test
  ]

prop_FunTypeReadShowIdentity :: FunType -> Bool
prop_FunTypeReadShowIdentity fun =
  read (show fun) == fun

prop_funTypeEquality :: PGF -> Property
prop_funTypeEquality pgf =
  let
    grammar = pgfToGrammar pgf
    funs = functions pgf
  in
    property $ and $ map (\f -> getFunTypeWithPGF pgf f == getFunTypeWithGrammar grammar (showCId f)) funs

prop_grammarLexRulesNotEmpty :: Grammar -> Property
prop_grammarLexRulesNotEmpty g = property $ not $ null $ lexrules g

prop_grammarSynRulesNotEmpty :: Grammar -> Property
prop_grammarSynRulesNotEmpty g = property $ not $ null $ synrules g

prop_grammarHasRulesForAllCats :: Grammar -> Property
prop_grammarHasRulesForAllCats g =
  let
    test c =
      property $ not $ null $ getRulesList (getAllRules g) [c]
    cats = nub $ concat $ map (\(Function _ (Fun c cs)) -> c:cs) $ (getAllRules g)
  in
    (not $ isEmptyGrammar g) ==> conjoin (map test cats)

hunit_tests = TestList [eq_tests,show_tests,grammar_function_tests]


quickcheck_tests :: [(TestName,Property)]
quickcheck_tests = [
  ("Grammar FunType show read equality",property prop_FunTypeReadShowIdentity),
  ("Grammar has lexical rules",property prop_grammarLexRulesNotEmpty),
  ("Grammar has syntactic rules",property prop_grammarSynRulesNotEmpty),
  ("Grammar has rules for all categories",property prop_grammarHasRulesForAllCats)
  ]
