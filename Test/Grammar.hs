{- | Implements several tests to control the validy of the program
-}
module Test.Grammar where
import PGF
import PGF.Internal
import Muste.Grammar.Internal
import Test.HUnit.Text
import Test.HUnit.Base
import Data.Maybe
import qualified Data.Map as M
import Control.Monad
import Data.Set (Set(..),empty,fromList)
-- HUnit tests
hunit_Eq_Grammar_eq_test =
  let
    grammar1 = Grammar (mkCId "S")
      [
        (Function (mkCId "a") (Fun (mkCId "A") [])),
        (Function (mkCId "b") (Fun (mkCId "B") [])),
        (Function (mkCId "c") (Fun (mkCId "C") [])),
        (Function (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])),
        (Function (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")])),
        (Function (mkCId "s") (Fun (mkCId "S") [(mkCId "A")]))
      ]
      emptyPGF
    grammar2 = Grammar (mkCId "A") [] emptyPGF
    pgf = readPGF "gf/ABCAbs.pgf"
    grammar3 = pgf >>= (return . pgfToGrammar)
  in
    TestList [
    TestLabel "Empty grammar" $ ( emptyGrammar == emptyGrammar ~?= True ),
    TestLabel "Simple Grammar reflexivity" $ ( grammar1 == grammar1 ~?= True ),
    TestLabel "Inequality 1" $ ( grammar1 == grammar2 ~?= False ),
    TestLabel "Inequality 2" $ ( grammar2 == grammar1 ~?= False ),
    TestLabel "Complex grammar" $ TestCase $ join $ liftM (\g -> grammar1 == g @?= True) grammar3
    ]
    
hunit_Show_FunType_show_test =
  let
    type1 = NoType
    type2 = (Fun (mkCId "A") [])
    type3 = (Fun (mkCId "A") [(mkCId "A")])
    type4 = (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
  in
    TestList [
    TestLabel "No Type" $ ( show type1 ~?= "()" ),
    TestLabel "Simple Type" $ ( show type2 ~?= "(A)" ),
    TestLabel "Function Type" $ ( show type3 ~?= "(A -> A)" ),
    TestLabel "Function Type" $ ( show type4 ~?= "(A -> B -> A)" )
    ]

hunit_Show_Rule_show_test =
  let
    fun1 = Function (mkCId "f1") NoType
    fun2 = Function (mkCId "f2") (Fun (mkCId "A") [])
    fun3 = Function (mkCId "f3") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])
  in
    TestList [
    TestLabel "No Type" $ ( show fun1 ~?= "f1 : ()" ),
    TestLabel "Simple Type" $ ( show fun2 ~?= "f2 : (A)" ),
    TestLabel "Function Type" $ ( show fun3 ~?= "f3 : (A -> B -> A)" )
    ]

hunit_Show_Grammar_show_test =
  let
    grammar1 = Grammar (mkCId "S") [] emptyPGF
    grammar2 = Grammar (mkCId "A")
      [
        (Function (mkCId "f1") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])),
        (Function (mkCId "f2") (Fun (mkCId "B") [(mkCId "B"),(mkCId "B")]))
      ]
      emptyPGF
  in
    TestList [
    TestLabel "Empty Grammar" $ ( show grammar1 ~?= "Startcat: S\nRules: \n" ),
    TestLabel "Simple Grammar" $ ( show grammar2 ~?= "Startcat: A\nRules: \n\tf1 : (A -> B -> A)\n \tf2 : (B -> B -> B)\n" )
    ]

hunit_Read_FunType_readsPrec_test =
  let
    str1 = "A"
    str2 = "(A)"
    type1 = (Fun (mkCId "A") [])
    str3 = "A->B"
    str4 = "A -> B"
    str5 = "(A->B)"
    str6 = "(A -> B)"
    str7 = "( A -> B )"
    type2 = (Fun (mkCId "B") [(mkCId "A")])
    str8 = ""
    str9 = "_"
    str10 = "###"
    str11 = "->"
    str12 = "-> A"
    str13 = "A ->"
  in
    TestList [
    TestLabel "Simple Type 1" $ ( readsPrec 0 str1 ~?= [(type1, "")] ),
    TestLabel "Simple Type 2" $ ( readsPrec 0 str2 ~?= [(type1, "")] ),
    TestLabel "Simple Type with rest 1" $ ( readsPrec 0 ( str2 ++ "###" ) ~?= [(type1, "###")] ),
    TestLabel "Simple Type with rest 2" $ ( readsPrec 0 ( str2 ++ "   ###" ) ~?= [(type1, "   ###")] ),
    TestLabel "Function Type 1" $ ( readsPrec 0 str3 ~?= [(type2, "")] ),
    TestLabel "Function Type 2" $ ( readsPrec 0 str4 ~?= [(type2, "")] ),
    TestLabel "Function Type 3" $ ( readsPrec 0 str5 ~?= [(type2, "")] ),
    TestLabel "Function Type 4" $ ( readsPrec 0 str6 ~?= [(type2, "")] ),
    TestLabel "Function Type 5" $ ( readsPrec 0 str7 ~?= [(type2, "")] ),
    TestLabel "Function Type with rest 1" $ ( readsPrec 0 ( str6 ++ "###" ) ~?= [(type2, "###")] ),
    TestLabel "Function Type with rest 2" $ ( readsPrec 0 ( str6 ++ "   ###" ) ~?= [(type2, "   ###")] ),
    TestLabel "Empty String" $ ( ( readsPrec 0 ( str8 ) :: [(FunType,String)] ) ~?= [(NoType,"")] ),
    TestLabel "Wildcard" $ ( ( readsPrec 0 ( str9 ) :: [(FunType,String)] ) ~?= [(NoType,"_")] ),
    TestLabel "Three Hashes" $ ( ( readsPrec 0 ( str10 ) :: [(FunType,String)] ) ~?= [(NoType,"###")] ),
    -- Nor really intended, but does it any harm?
    TestLabel "Arrow" $ ( ( readsPrec 0 ( str11 ) :: [(FunType,String)] ) ~?= [(NoType,"")] ),
    TestLabel "Arrow A" $ ( ( readsPrec 0 ( str12 ) :: [(FunType,String)] ) ~?= [(type1,"")] ),
    TestLabel "A Arrow" $ ( ( readsPrec 0 ( str13 ) :: [(FunType,String)] ) ~?= [(type1,"")] )
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
    grammar1 = Grammar (mkCId "S") [(Function (mkCId "f") (Fun (mkCId "S") [(mkCId "A")])),(Function (mkCId "a") (Fun (mkCId "A") []))] emptyPGF
    pgf = readPGF "gf/ABCAbs.pgf"
    grammar2 = pgf >>= (\p -> return $ Grammar wildCId [] p)
  in
    TestList [
    TestLabel "Empty Grammar" $ isEmptyGrammar emptyGrammar ~?= True,
    TestLabel "Almost empty Grammar with a name" $ isEmptyGrammar grammar1 ~?= False,
    TestLabel "Grammar without a name" $ TestCase $ grammar2 >>= (\g -> isEmptyGrammar g @?= False),
    TestLabel "Complete grammar from PGF" $ TestCase $ pgf >>= (\g -> isEmptyGrammar (pgfToGrammar g) @?= False)
    ]
  
hunit_readId_test =
  let
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
    TestLabel "Unacceptable Letter 1" $ ( readId str1 ~?= Nothing ),
    TestLabel "Unacceptable Letter 2" $ ( readId str2 ~?= Nothing ),
    TestLabel "Unacceptable Letter 3" $ ( readId str3 ~?= Just (mkCId "?","") ),
    TestLabel "Single Letter 1" $ ( readId str4 ~?= Just (mkCId "A","") ),
    TestLabel "Single Letter 2" $ ( readId str5 ~?= Nothing ),
    TestLabel "Multiple Letters 1" $ ( readId str6 ~?= Just (mkCId "_A","") ),
    TestLabel "Multiple Letters 2" $ ( readId str7 ~?= Just (mkCId "?A","") ),
    TestLabel "Multiple Letters 3" $ ( readId str8 ~?= Just (mkCId "?\'?\'","") ),
    TestLabel "Multiple Letters 4" $ ( readId str9 ~?= Just (mkCId "ABC","") ),
    TestLabel "Multiple Letters 5" $ ( readId str10 ~?= Just (mkCId "Abc","") ),
    TestLabel "Multiple Letters 6" $ ( readId str11 ~?= Just (mkCId "A_B_C","") ),
    TestLabel "Multiple Letters 7" $ ( readId str12 ~?= Just (mkCId "A",".B.C") ),
    TestLabel "Multiple Letters 8" $ ( readId str13 ~?= Just (mkCId "A","?") ),
    TestLabel "Single Letter with rest 1" $ ( readId (str4 ++ "###") ~?= Just (mkCId "A","###") ),
    TestLabel "Single Letter with rest 2" $ ( readId (str4 ++ " ###") ~?= Just (mkCId "A"," ###") ),
    TestLabel "Single Letter with rest 1" $ ( readId (str9 ++ "###") ~?= Just (mkCId "ABC","###") ),
    TestLabel "Single Letter with rest 2" $ ( readId (str9 ++ " ###") ~?= Just (mkCId "ABC"," ###") )
    ]

hunit_getFunType_test =
  let
    pgf = readPGF "gf/ABCAbs.pgf"
  in
    TestList [
    TestLabel "Empty PGF" $ getFunType emptyPGF (mkCId "f") ~?= NoType,
    TestLabel "Existing Constant" $ TestCase $ pgf >>= (\g -> getFunType g (mkCId "a") @?= (Fun (mkCId "A") [])),
    TestLabel "Existing Function" $ TestCase $ pgf >>= (\g -> getFunType g (mkCId "f") @?= (Fun (mkCId "A") [(mkCId "A"), (mkCId "B")])),
    TestLabel "Non-Existing Function" $ TestCase $ pgf >>= (\g -> getFunType g (mkCId "foo") @?= NoType)
    ]

hunit_getFunCat_test =
  TestList [
  TestLabel "NoType" $ getFunCat NoType ~?= wildCId,
  TestLabel "Constant" $ getFunCat (Fun (mkCId "A") []) ~?= (mkCId "A"),
  TestLabel "Constant" $ getFunCat (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")]) ~?= (mkCId "A")
  ]

hunit_getRuleCat_test =
  TestList [
  TestLabel "NoType" $ getRuleCat (Function (mkCId "f") NoType) ~?= wildCId,
  TestLabel "Constant" $ getRuleCat (Function (mkCId "f") (Fun (mkCId "A") [])) ~?= (mkCId "A"),
  TestLabel "Constant" $ getRuleCat (Function (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])) ~?= (mkCId "A")
  ]

hunit_getRules_test =
  let
    rule1 = (Function (mkCId "r1") (Fun (mkCId "A") []))
    rule2 = (Function (mkCId "r2") (Fun (mkCId "A") [(mkCId "A")]))
    rule3 = (Function (mkCId "r3") (Fun (mkCId "B") [(mkCId "A")]))
    rule4 = (Function (mkCId "r4") (Fun (mkCId "A") [(mkCId "A"),(mkCId "A")]))
    rule5 = (Function (mkCId "r5") NoType)
    grammar = Grammar (mkCId "S")
      [ rule1, rule2, rule3, rule4, rule5 ]
      emptyPGF
  in
    TestList [
    TestLabel "Empty Grammar" $ getRules emptyGrammar [] ~?= empty,
    TestLabel "No categories" $ getRules grammar [] ~?= empty,
    TestLabel "No match" $ getRules grammar [(mkCId "Z")] ~?= empty,
    TestLabel "One match" $ getRules grammar [(mkCId "B")] ~?= fromList [rule3],
    TestLabel "Three matches" $ getRules grammar [(mkCId "A")] ~?= fromList [rule1, rule2, rule4],
    TestLabel "All matches" $ getRules grammar [(mkCId "A"),(mkCId "B"),wildCId] ~?= fromList (rules grammar)
    ]
    
hunit_pgfToGrammar_test =
  let
    pgf = readPGF "gf/ABCAbs.pgf"
    grammar = pgf >>= return . (Grammar
      (mkCId "S")
      [
        (Function (mkCId "a") (Fun (mkCId "A") [])),
        (Function (mkCId "b") (Fun (mkCId "B") [])),
        (Function (mkCId "c") (Fun (mkCId "C") [])),
        (Function (mkCId "f") (Fun (mkCId "A") [(mkCId "A"),(mkCId "B")])),
        (Function (mkCId "g") (Fun (mkCId "B") [(mkCId "B"),(mkCId "C")])),
        (Function (mkCId "s") (Fun (mkCId "S") [(mkCId "A")]))
      ])
  in
    TestList [
    TestLabel "Non-empty PGF" $ TestCase $ join $ liftM2 (@?=) (pgf >>= return . pgfToGrammar) grammar
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
  TestLabel "Read FunType readsPrec" hunit_Read_FunType_readsPrec_test
  ]

grammar_function_tests =
  TestList [
  TestLabel "isEmptyPGF" hunit_isEmptyPGF_test,
  TestLabel "isEmptyGrammar" hunit_isEmptyGrammar_test,
  TestLabel "readId" hunit_readId_test,
  TestLabel "getFunType" hunit_getFunType_test,
  TestLabel "getFunCat" hunit_getFunCat_test,
  TestLabel "getRuleCat" hunit_getRuleCat_test,
  TestLabel "getRules" hunit_getRuleCat_test,
  TestLabel "pgfToGrammar" hunit_pgfToGrammar_test
  ]

hunit_tests = TestList [eq_tests,show_tests,read_tests,grammar_function_tests] --, tree_function_tests]
