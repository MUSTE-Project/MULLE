-- | Data used for inititializing the database

module Data (exercises, getLessons) where

import qualified Config

import Muste.Tree
import Muste.Grammar

exercises :: [(TTree, TTree, String)]
exercises =
  [ ( TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefsg" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "vinum_N" (Fun "N" []) []]],TNode "complVA" (Fun "VP" ["VA","AP"]) [TNode "copula_VA" (Fun "VA" []) [],TNode "useA" (Fun "AP" ["A"]) [TNode "sapiens_A" (Fun "A" []) []]]]]]
    , TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePron" (Fun "NP" ["Pron"]) [TNode "he_PP" (Fun "Pron" []) []],TNode "complVA" (Fun "VP" ["VA","AP"]) [TNode "copula_VA" (Fun "VA" []) [],TNode "useA" (Fun "AP" ["A"]) [TNode "sapiens_A" (Fun "A" []) []]]]]]
    , "Prima Pars"
    )
  , ( TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePN" (Fun "NP" ["PN"]) [TNode "Augustus_PN" (Fun "PN" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "tenere_V2" (Fun "V2" []) [],TNode "useCNdefsg" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "imperium_N" (Fun "N" []) []]]]]]]
    , TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefsg" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "imperator_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "tenere_V2" (Fun "V2" []) [],TNode "useCNdefsg" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "imperium_N" (Fun "N" []) []]]]]]]
    , "Prima Pars"
    )
  , ( TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePN" (Fun "NP" ["PN"]) [TNode "Augustus_PN" (Fun "PN" []) []],TNode "complVA" (Fun "VP" ["VA","AP"]) [TNode "copula_VA" (Fun "VA" []) [],TNode "useA" (Fun "AP" ["A"]) [TNode "felix_A" (Fun "A" []) []]]]]]
    , TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefsg" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "amicus_N" (Fun "N" []) []]],TNode "complVA" (Fun "VP" ["VA","AP"]) [TNode "copula_VA" (Fun "VA" []) [],TNode "useA" (Fun "AP" ["A"]) [TNode "felix_A" (Fun "A" []) []]]]]]
    , "Prima Pars"
    )
  , ( TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePN" (Fun "NP" ["PN"]) [TNode "Augustus_PN" (Fun "PN" []) []],TNode "complVA" (Fun "VP" ["VA","AP"]) [TNode "copula_VA" (Fun "VA" []) [],TNode "useA" (Fun "AP" ["A"]) [TNode "felix_A" (Fun "A" []) []]]]]]
    , TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefsg" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "pater_N" (Fun "N" []) []]],TNode "complVA" (Fun "VP" ["VA","AP"]) [TNode "copula_VA" (Fun "VA" []) [],TNode "useA" (Fun "AP" ["A"]) [TNode "felix_A" (Fun "A" []) []]]]]]
    , "Prima Pars"
    )
  , ( TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePN" (Fun "NP" ["PN"]) [TNode "Augustus_PN" (Fun "PN" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "copula_V2" (Fun "V2" []) [],TNode "useCNdefsg" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "imperator_N" (Fun "N" []) []]]]]]]
    , TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePN" (Fun "NP" ["PN"]) [TNode "Augustus_PN" (Fun "PN" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "copula_V2" (Fun "V2" []) [],TNode "useCNdefsg" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "amicus_N" (Fun "N" []) []]]]]]]
    , "Prima Pars"
    )
  , ( TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePN" (Fun "NP" ["PN"]) [TNode "Augustus_PN" (Fun "PN" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "copula_V2" (Fun "V2" []) [],TNode "useCNdefsg" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "amicus_N" (Fun "N" []) []]]]]]]
    , TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePN" (Fun "NP" ["PN"]) [TNode "Augustus_PN" (Fun "PN" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "copula_V2" (Fun "V2" []) [],TNode "useCNdefsg" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "imperator_N" (Fun "N" []) []]]]]]]
    , "Prima Pars"
    )
  , ( TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePN" (Fun "NP" ["PN"]) [TNode "Augustus_PN" (Fun "PN" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "copula_V2" (Fun "V2" []) [],TNode "useCNdefsg" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "imperator_N" (Fun "N" []) []]]]]]]
    , TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePN" (Fun "NP" ["PN"]) [TNode "Augustus_PN" (Fun "PN" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "copula_V2" (Fun "V2" []) [],TNode "useCNdefsg" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "pater_N" (Fun "N" []) []]]]]]]
    , "Prima Pars"
    )
  , ( TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePN" (Fun "NP" ["PN"]) [TNode "Augustus_PN" (Fun "PN" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "copula_V2" (Fun "V2" []) [],TNode "useCNdefsg" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "pater_N" (Fun "N" []) []]]]]]]
    , TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePN" (Fun "NP" ["PN"]) [TNode "Augustus_PN" (Fun "PN" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "copula_V2" (Fun "V2" []) [],TNode "useCNdefsg" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "imperator_N" (Fun "N" []) []]]]]]]
    , "Prima Pars"
    )
  , ( TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "apposCNdefsg" (Fun "NP" ["CN","PN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Caesar_N" (Fun "N" []) []],TNode "Augustus_PN" (Fun "PN" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "vincere_V2" (Fun "V2" []) [],TNode "usePN" (Fun "NP" ["PN"]) [TNode "Gallia_PN" (Fun "PN" []) []]]]]]
    , TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "apposCNdefsg" (Fun "NP" ["CN","PN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Caesar_N" (Fun "N" []) []],TNode "Augustus_PN" (Fun "PN" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "vincere_V2" (Fun "V2" []) [],TNode "usePN" (Fun "NP" ["PN"]) [TNode "Africa_PN" (Fun "PN" []) []]]]]]
    , "Prima Pars"
    )
  , ( TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "apposCNdefsg" (Fun "NP" ["CN","PN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Caesar_N" (Fun "N" []) []],TNode "Augustus_PN" (Fun "PN" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "vincere_V2" (Fun "V2" []) [],TNode "usePN" (Fun "NP" ["PN"]) [TNode "Africa_PN" (Fun "PN" []) []]]]]]
    , TNode "useS" (Fun "CS" ["S"]) [TNode "useCl" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "apposCNdefsg" (Fun "NP" ["CN","PN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Caesar_N" (Fun "N" []) []],TNode "Augustus_PN" (Fun "PN" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "vincere_V2" (Fun "V2" []) [],TNode "usePN" (Fun "NP" ["PN"]) [TNode "Gallia_PN" (Fun "PN" []) []]]]]]
    , "Prima Pars"
    )
  ]

-- TODO Make a newtype for this (and instances of 'FromROW' and
-- 'ToROW',
type Lesson = (String,String,String,String,String,Int,Int,Int)

mkLesson :: Lesson -> IO Lesson
mkLesson (f,u,n,k,y,e,a,h) = do
  n' <- Config.getGrammar n
  pure (f,u,n',k,y,e,a,h)

getLessons :: IO [Lesson]
getLessons = mapM mkLesson
  [ ( "Prima Pars"
    , "Den första Lektionen fran boken \"Novo modo\""
    , "Prima"
    , "PrimaLat"
    , "PrimaSwe"
    , 5
    , 1
    , 1
    )
  , ( "Secunda Pars"
    , "Den andra Lektionen fran boken \"Novo modo\""
    , "Secunda"
    , "SecundaLat"
    , "SecundaSwe"
    , 8
    , 1
    , 1
    )
  , ( "Tertia Pars"
    , "Den tredje Lektionen fran boken \"Novo modo\""
    , "Tertia"
    , "TertiaLat"
    , "TertiaSwe"
    , 12
    , 0
    , 1
    )
  , ( "Quarta Pars"
    , "Den fjärde Lektionen fran boken \"Novo modo\""
    , "Quarta"
    , "QuartaLat"
    , "QuartaSwe"
    , 15
    , 0
    , 1
    )
  ]
