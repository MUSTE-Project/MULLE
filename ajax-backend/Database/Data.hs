-- | Data used for inititializing the database

module Database.Data (exercises) where

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
