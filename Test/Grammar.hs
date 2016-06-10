{- | Implements several tests to control the validy of the program
-}
module Test.Grammar where
import PGF
import PGF.Internal
import Muste.Grammar.Internal
import Test.HUnit.Text
import Test.HUnit.Base
import Data.Maybe

-- HUnit tests
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
    TestLabel "Function Type with rest 2" $ ( readsPrec 0 ( str6 ++ "   ###" ) ~?= [(type2, "   ###")] )
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
  TestLabel "readId" hunit_readId_test
  -- TestLabel "readFunType" hunit_readFunType_test,
  -- TestLabel "getChildCats" hunit_getChildCats_test,
  -- TestLabel "typeCheck" hunit_typeCheck_test,
  -- TestLabel "typeCheck" hunit_fixTypes_test
  ]
  
hunit_tests =
  do
    let tests = TestList [show_tests,read_tests,grammar_function_tests] --, tree_function_tests]
    runTestTT tests
    
-- Main
main =
  do
    putStrLn "HUnite tests:"
    hunit_tests
