{-# Language CPP #-}
-- | Data used for inititializing the database

module Data (exercises, lessons) where

#if MIN_VERSION_base(4,11,0)
#else
import Data.Semigroup (Semigroup((<>)))
#endif

import Muste.Tree

-- TODO Make a newtype for this (and instances of 'FromROW' and
-- 'ToROW',
type Lesson = (String,String,String,String,String,Int,Int,Int)

lessons :: [Lesson]
lessons =
  [ ( "Prima Pars"
    , "Den första Lektionen fran boken \"Novo modo\""
    , "novo_modo/Prima"
    , "PrimaLat"
    , "PrimaSwe"
    , 5
    , 1
    , 1
    )
  , ( "Secunda Pars"
    , "Den andra Lektionen fran boken \"Novo modo\""
    , "novo_modo/Secunda"
    , "SecundaLat"
    , "SecundaSwe"
    , 8
    , 1
    , 1
    )
  , ( "Tertia Pars"
    , "Den tredje Lektionen fran boken \"Novo modo\""
    , "novo_modo/Tertia"
    , "TertiaLat"
    , "TertiaSwe"
    , 12
    , 0
    , 1
    )
  , ( "Quarta Pars"
    , "Den fjärde Lektionen fran boken \"Novo modo\""
    , "novo_modo/Quarta"
    , "QuartaLat"
    , "QuartaSwe"
    , 15
    , 0
    , 1
    )
  ]

exercises :: [(TTree, TTree, String)]
exercises = primaPars <> secundaPars

primaPars :: [(TTree, TTree, String)]
primaPars =
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

secundaPars :: [(TTree, TTree, String)]
secundaPars =
  [(TNode "useS" (Fun "CS" ["S"]) [TNode "impS" (Fun "S" ["Pron","VP"]) [TNode "they_PP" (Fun "Pron" []) [],TNode "useVV" (Fun "VP" ["VV"]) [TNode "nolle_VV" (Fun "VV" []) []]]],TNode "useS" (Fun "CS" ["S"]) [TNode "presS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePron" (Fun "NP" ["Pron"]) [TNode "they_PP" (Fun "Pron" []) []],TNode "intransV" (Fun "VP" ["V"]) [TNode "gaudere_V" (Fun "V" []) []]]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "presS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePron" (Fun "NP" ["Pron"]) [TNode "they_PP" (Fun "Pron" []) []],TNode "intransV" (Fun "VP" ["V"]) [TNode "gaudere_V" (Fun "V" []) []]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "impS" (Fun "S" ["Pron","VP"]) [TNode "they_PP" (Fun "Pron" []) [],TNode "useVV" (Fun "VP" ["VV"]) [TNode "nolle_VV" (Fun "VV" []) []]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "impS" (Fun "S" ["Pron","VP"]) [TNode "nos_Pron" NoType [],TNode "useVV" (Fun "VP" ["VV"]) [TNode "velle_VV" (Fun "VV" []) []]]],TNode "useS" (Fun "CS" ["S"]) [TNode "presS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePron" (Fun "NP" ["Pron"]) [TNode "nos_Pron" NoType []],TNode "intransV" (Fun "VP" ["V"]) [TNode "venire_V" (Fun "V" []) []]]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "presS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePron" (Fun "NP" ["Pron"]) [TNode "nos_Pron" NoType []],TNode "intransV" (Fun "VP" ["V"]) [TNode "venire_V" (Fun "V" []) []]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "impS" (Fun "S" ["Pron","VP"]) [TNode "nos_Pron" NoType [],TNode "useVV" (Fun "VP" ["VV"]) [TNode "velle_VV" (Fun "VV" []) []]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Romanus_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "vincere_V2" (Fun "V2" []) [],TNode "usePron" (Fun "NP" ["Pron"]) [TNode "they_PP" (Fun "Pron" []) []]]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePron" (Fun "NP" ["Pron"]) [TNode "they_PP" (Fun "Pron" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "docere_V2" (Fun "V2" []) [],TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Romanus_N" (Fun "N" []) []]]]]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePron" (Fun "NP" ["Pron"]) [TNode "they_PP" (Fun "Pron" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "docere_V2" (Fun "V2" []) [],TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Romanus_N" (Fun "N" []) []]]]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Romanus_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "vincere_V2" (Fun "V2" []) [],TNode "usePron" (Fun "NP" ["Pron"]) [TNode "they_PP" (Fun "Pron" []) []]]]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "vir_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "rapere_V2" (Fun "V2" []) [],TNode "usePron" (Fun "NP" ["Pron"]) [TNode "they_PP" (Fun "Pron" []) []]]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePron" (Fun "NP" ["Pron"]) [TNode "they_PP" (Fun "Pron" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "invitare_V2" (Fun "V2" []) [],TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "vir_N" (Fun "N" []) []]]]]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePron" (Fun "NP" ["Pron"]) [TNode "they_PP" (Fun "Pron" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "invitare_V2" (Fun "V2" []) [],TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "vir_N" (Fun "N" []) []]]]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "vir_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "rapere_V2" (Fun "V2" []) [],TNode "usePron" (Fun "NP" ["Pron"]) [TNode "they_PP" (Fun "Pron" []) []]]]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Etruscus_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "observare_V2" (Fun "V2" []) [],TNode "useCNindefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "auspicium_N" (Fun "N" []) []]]]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePron" (Fun "NP" ["Pron"]) [TNode "they_PP" (Fun "Pron" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "copula_V2" (Fun "V2" []) [],TNode "useCNindefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "agricola_N" (Fun "N" []) []]]]]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Romanus_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "copula_V2" (Fun "V2" []) [],TNode "useCNindefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "agricola_N" (Fun "N" []) []]]]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePron" (Fun "NP" ["Pron"]) [TNode "they_PP" (Fun "Pron" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "observare_V2" (Fun "V2" []) [],TNode "useCNindefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "auspicium_N" (Fun "N" []) []]]]]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefsg" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "rex_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "observare_V2" (Fun "V2" []) [],TNode "useCNindefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "terra_N" (Fun "N" []) []]]]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePron" (Fun "NP" ["Pron"]) [TNode "they_PP" (Fun "Pron" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "copula_V2" (Fun "V2" []) [],TNode "useCNindefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "vir_N" (Fun "N" []) []]]]]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Romanus_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "copula_V2" (Fun "V2" []) [],TNode "useCNindefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "vir_N" (Fun "N" []) []]]]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefsg" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "rex_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "observare_V2" (Fun "V2" []) [],TNode "useCNindefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "terra_N" (Fun "N" []) []]]]]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "advS" (Fun "S" ["Adv","S"]) [TNode "autem_Adv" (Fun "Adv" []) [],TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Sabinus_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "habere_V2" (Fun "V2" []) [],TNode "useCNindefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "femina_N" (Fun "N" []) []]]]]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "advS" (Fun "S" ["Adv","S"]) [TNode "autem_Adv" (Fun "Adv" []) [],TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Romanus_N" (Fun "N" []) []]],TNode "complVA" (Fun "VP" ["VA","AP"]) [TNode "copula_VA" (Fun "VA" []) [],TNode "useA" (Fun "AP" ["A"]) [TNode "fallax_A" (Fun "A" []) []]]]]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "advS" (Fun "S" ["Adv","S"]) [TNode "autem_Adv" (Fun "Adv" []) [],TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Romanus_N" (Fun "N" []) []]],TNode "complVA" (Fun "VP" ["VA","AP"]) [TNode "copula_VA" (Fun "VA" []) [],TNode "useA" (Fun "AP" ["A"]) [TNode "fallax_A" (Fun "A" []) []]]]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "advS" (Fun "S" ["Adv","S"]) [TNode "autem_Adv" (Fun "Adv" []) [],TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Sabinus_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "habere_V2" (Fun "V2" []) [],TNode "useCNindefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "femina_N" (Fun "N" []) []]]]]]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "advS" (Fun "S" ["Adv","S"]) [TNode "etiam_Adv" (Fun "Adv" []) [],TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Sabinus_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "habere_V2" (Fun "V2" []) [],TNode "useCNdefsg" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "religio_N" (Fun "N" []) []]]]]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "advS" (Fun "S" ["Adv","S"]) [TNode "iam_Adv" (Fun "Adv" []) [],TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Romanus_N" (Fun "N" []) []]],TNode "complVA" (Fun "VP" ["VA","AP"]) [TNode "copula_VA" (Fun "VA" []) [],TNode "useA" (Fun "AP" ["A"]) [TNode "victus_A" (Fun "A" []) []]]]]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "advS" (Fun "S" ["Adv","S"]) [TNode "iam_Adv" (Fun "Adv" []) [],TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Romanus_N" (Fun "N" []) []]],TNode "complVA" (Fun "VP" ["VA","AP"]) [TNode "copula_VA" (Fun "VA" []) [],TNode "useA" (Fun "AP" ["A"]) [TNode "victus_A" (Fun "A" []) []]]]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "advS" (Fun "S" ["Adv","S"]) [TNode "etiam_Adv" (Fun "Adv" []) [],TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Sabinus_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "habere_V2" (Fun "V2" []) [],TNode "useCNdefsg" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "religio_N" (Fun "N" []) []]]]]]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Sabinus_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "amare_V2" (Fun "V2" []) [],TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "liber_N" (Fun "N" []) []]]]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "negPastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePron" (Fun "NP" ["Pron"]) [TNode "they_PP" (Fun "Pron" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "copula_V2" (Fun "V2" []) [],TNode "useCNindefpl" (Fun "NP" ["CN"]) [TNode "attribCN" (Fun "CN" ["AP","CN"]) [TNode "useA" (Fun "AP" ["A"]) [TNode "Romanus_A" (Fun "A" []) []],TNode "useN" (Fun "CN" ["N"]) [TNode "liber_N" (Fun "N" []) []]]]]]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "negPastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "iuvenis_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "copula_V2" (Fun "V2" []) [],TNode "useCNindefpl" (Fun "NP" ["CN"]) [TNode "attribCN" (Fun "CN" ["AP","CN"]) [TNode "useA" (Fun "AP" ["A"]) [TNode "Romanus_A" (Fun "A" []) []],TNode "useN" (Fun "CN" ["N"]) [TNode "liber_N" (Fun "N" []) []]]]]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Sabinus_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "amare_V2" (Fun "V2" []) [],TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "liber_N" (Fun "N" []) []]]]]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Sabinus_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "amare_V2" (Fun "V2" []) [],TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "mulier_N" (Fun "N" []) []]]]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePron" (Fun "NP" ["Pron"]) [TNode "they_PP" (Fun "Pron" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "copula_V2" (Fun "V2" []) [],TNode "useCNindefpl" (Fun "NP" ["CN"]) [TNode "attribCN" (Fun "CN" ["AP","CN"]) [TNode "useA" (Fun "AP" ["A"]) [TNode "Sabinus_A" (Fun "A" []) []],TNode "useN" (Fun "CN" ["N"]) [TNode "liber_N" (Fun "N" []) []]]]]]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "iuvenis_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "copula_V2" (Fun "V2" []) [],TNode "useCNindefpl" (Fun "NP" ["CN"]) [TNode "attribCN" (Fun "CN" ["AP","CN"]) [TNode "useA" (Fun "AP" ["A"]) [TNode "Sabinus_A" (Fun "A" []) []],TNode "useN" (Fun "CN" ["N"]) [TNode "liber_N" (Fun "N" []) []]]]]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Sabinus_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "amare_V2" (Fun "V2" []) [],TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "mulier_N" (Fun "N" []) []]]]]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "presS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Sabinus_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "dicere_V2" (Fun "V2" []) [],TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "attribCN" (Fun "CN" ["AP","CN"]) [TNode "useA" (Fun "AP" ["A"]) [TNode "Romanus_A" (Fun "A" []) []],TNode "useN" (Fun "CN" ["N"]) [TNode "vir_N" (Fun "N" []) []]]]]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "presS" (Fun "S" ["Cl"]) [TNode "useVVCl" (Fun "Cl" ["NP","VV","VP"]) [TNode "usePron" (Fun "NP" ["Pron"]) [TNode "they_PP" (Fun "Pron" []) []],TNode "velle_VV" (Fun "VV" []) [],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "occidere_V2" (Fun "V2" []) [],TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "attribCN" (Fun "CN" ["AP","CN"]) [TNode "useA" (Fun "AP" ["A"]) [TNode "Romanus_A" (Fun "A" []) []],TNode "useN" (Fun "CN" ["N"]) [TNode "vir_N" (Fun "N" []) []]]]]]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Romanus_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "contendere_V2" (Fun "V2" []) [],TNode "usePron" (Fun "NP" ["Pron"]) [TNode "they_PP" (Fun "Pron" []) []]]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePron" (Fun "NP" ["Pron"]) [TNode "they_PP" (Fun "Pron" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "contendere_V2" (Fun "V2" []) [],TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Romanus_N" (Fun "N" []) []]]]]]],"Secunda Pars")
  ,(TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Romanus_N" (Fun "N" []) []]],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "docere_V2" (Fun "V2" []) [],TNode "usePron" (Fun "NP" ["Pron"]) [TNode "they_PP" (Fun "Pron" []) []]]]]],TNode "useS" (Fun "CS" ["S"]) [TNode "pastS" (Fun "S" ["Cl"]) [TNode "simpleCl" (Fun "Cl" ["NP","VP"]) [TNode "usePron" (Fun "NP" ["Pron"]) [TNode "they_PP" (Fun "Pron" []) []],TNode "transV" (Fun "VP" ["V2","NP"]) [TNode "docere_V2" (Fun "V2" []) [],TNode "useCNdefpl" (Fun "NP" ["CN"]) [TNode "useN" (Fun "CN" ["N"]) [TNode "Romanus_N" (Fun "N" []) []]]]]]],"Secunda Pars")
  ]
