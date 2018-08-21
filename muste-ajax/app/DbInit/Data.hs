{-# Language CPP, TemplateHaskell #-}
-- | Data used for inititializing the database

module DbInit.Data (exercises, lessons) where

import Muste.Tree
import Muste.Grammar (tree)

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

-- | List of exercises group by the lesson they belong to.  The lesson
-- is identified by 1. an identifier for the grammar for that lesson
-- and 2. by the name of that lesson (a PK in the DB).  Exercises are
-- identified by a pair of tree/language pairs.
exercises :: [(String, String, String, String, [(TTree, TTree)])]
exercises =
  [ ("novo_modo/Prima"  , "Prima Pars"  , "PrimaLat"  , "PrimaSwe"  , primaPars)
  , ("novo_modo/Secunda", "Secunda Pars", "SecundaLat", "SecundaSwe", secundaPars)
  ]

primaPars ∷ [(TTree, TTree)]
primaPars =
  [ ( ($(tree "novo_modo/Prima" "useS (useCl (simpleCl (useCNdefsg (useN vinum_N)) (complVA copula_VA (useA sapiens_A))))"))
    , ($(tree "novo_modo/Prima" "useS (useCl (simpleCl (usePron he_PP) (complVA copula_VA (useA sapiens_A))))"))
    )
  , ( ($(tree "novo_modo/Prima" "useS (useCl (simpleCl (usePN Augustus_PN) (transV tenere_V2 (useCNdefsg (useN imperium_N)))))"))
    , ($(tree "novo_modo/Prima" "useS (useCl (simpleCl (useCNdefsg (useN imperator_N)) (transV tenere_V2 (useCNdefsg (useN imperium_N)))))"))
    )
  , ( ($(tree "novo_modo/Prima" "useS (useCl (simpleCl (usePN Augustus_PN) (complVA copula_VA (useA felix_A))))"))
    , ($(tree "novo_modo/Prima" "useS (useCl (simpleCl (useCNdefsg (useN amicus_N)) (complVA copula_VA (useA felix_A))))"))
    )
  , ( ($(tree "novo_modo/Prima" "useS (useCl (simpleCl (usePN Augustus_PN) (complVA copula_VA (useA felix_A))))"))
    , ($(tree "novo_modo/Prima" "useS (useCl (simpleCl (useCNdefsg (useN pater_N)) (complVA copula_VA (useA felix_A))))"))
    )
  , ( ($(tree "novo_modo/Prima" "useS (useCl (simpleCl (usePN Augustus_PN) (transV copula_V2 (useCNdefsg (useN imperator_N)))))"))
    , ($(tree "novo_modo/Prima" "useS (useCl (simpleCl (usePN Augustus_PN) (transV copula_V2 (useCNdefsg (useN amicus_N)))))"))
    )
  , ( ($(tree "novo_modo/Prima" "useS (useCl (simpleCl (usePN Augustus_PN) (transV copula_V2 (useCNdefsg (useN amicus_N)))))"))
    , ($(tree "novo_modo/Prima" "useS (useCl (simpleCl (usePN Augustus_PN) (transV copula_V2 (useCNdefsg (useN imperator_N)))))"))
    )
  , ( ($(tree "novo_modo/Prima" "useS (useCl (simpleCl (usePN Augustus_PN) (transV copula_V2 (useCNdefsg (useN imperator_N)))))"))
    , ($(tree "novo_modo/Prima" "useS (useCl (simpleCl (usePN Augustus_PN) (transV copula_V2 (useCNdefsg (useN pater_N)))))"))
    )
  , ( ($(tree "novo_modo/Prima" "useS (useCl (simpleCl (usePN Augustus_PN) (transV copula_V2 (useCNdefsg (useN pater_N)))))"))
    , ($(tree "novo_modo/Prima" "useS (useCl (simpleCl (usePN Augustus_PN) (transV copula_V2 (useCNdefsg (useN imperator_N)))))"))
    )
  , ( ($(tree "novo_modo/Prima" "useS (useCl (simpleCl (apposCNdefsg (useN Caesar_N) Augustus_PN) (transV vincere_V2 (usePN Gallia_PN))))"))
    , ($(tree "novo_modo/Prima" "useS (useCl (simpleCl (apposCNdefsg (useN Caesar_N) Augustus_PN) (transV vincere_V2 (usePN Africa_PN))))"))
    )
  , ( ($(tree "novo_modo/Prima" "useS (useCl (simpleCl (apposCNdefsg (useN Caesar_N) Augustus_PN) (transV vincere_V2 (usePN Africa_PN))))"))
    , ($(tree "novo_modo/Prima" "useS (useCl (simpleCl (apposCNdefsg (useN Caesar_N) Augustus_PN) (transV vincere_V2 (usePN Gallia_PN))))"))
    )
  ]


-- Offending trees:
  --   ( ($(tree "novo_modo/Secunda" "useS (impS nos_Pron (useVV velle_VV))"))
  --   , ($(tree "novo_modo/Secunda" "useS (presS (simpleCl (usePron nos_Pron) (intransV venire_V)))"))
  --   )

  -- , ( ($(tree "novo_modo/Secunda" "useS (presS (simpleCl (usePron nos_Pron) (intransV venire_V)))"))
  --   , ($(tree "novo_modo/Secunda" "useS (impS nos_Pron (useVV velle_VV))"))
  --   )

secundaPars :: [(TTree, TTree)]
secundaPars =
  [ ( ($(tree "novo_modo/Secunda" "useS (impS they_PP (useVV nolle_VV))"))
    , ($(tree "novo_modo/Secunda" "useS (presS (simpleCl (usePron they_PP) (intransV gaudere_V)))"))
    )
  , ( ($(tree "novo_modo/Secunda" "useS (presS (simpleCl (usePron they_PP) (intransV gaudere_V)))"))
    , ($(tree "novo_modo/Secunda" "useS (impS they_PP (useVV nolle_VV))"))
    )
  , ( ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (useCNdefpl (useN Romanus_N)) (transV vincere_V2 (usePron they_PP))))"))
    , ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (usePron they_PP) (transV docere_V2 (useCNdefpl (useN Romanus_N)))))"))
    )
    , ( ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (usePron they_PP) (transV docere_V2 (useCNdefpl (useN Romanus_N)))))"))
    , ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (useCNdefpl (useN Romanus_N)) (transV vincere_V2 (usePron they_PP))))"))
    )
  , ( ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (useCNdefpl (useN vir_N)) (transV rapere_V2 (usePron they_PP))))"))
    , ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (usePron they_PP) (transV invitare_V2 (useCNdefpl (useN vir_N)))))"))
    )
  , ( ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (usePron they_PP) (transV invitare_V2 (useCNdefpl (useN vir_N)))))"))
    , ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (useCNdefpl (useN vir_N)) (transV rapere_V2 (usePron they_PP))))"))
    )
  , ( ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (useCNdefpl (useN Etruscus_N)) (transV observare_V2 (useCNindefpl (useN auspicium_N)))))"))
    , ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (usePron they_PP) (transV copula_V2 (useCNindefpl (useN agricola_N)))))"))
    )
  , ( ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (useCNdefpl (useN Romanus_N)) (transV copula_V2 (useCNindefpl (useN agricola_N)))))"))
    , ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (usePron they_PP) (transV observare_V2 (useCNindefpl (useN auspicium_N)))))"))
    )
  , ( ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (useCNdefsg (useN rex_N)) (transV observare_V2 (useCNindefpl (useN terra_N)))))"))
    , ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (usePron they_PP) (transV copula_V2 (useCNindefpl (useN vir_N)))))"))
    )
  , ( ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (useCNdefpl (useN Romanus_N)) (transV copula_V2 (useCNindefpl (useN vir_N)))))"))
    , ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (useCNdefsg (useN rex_N)) (transV observare_V2 (useCNindefpl (useN terra_N)))))"))
    )
  , ( ($(tree "novo_modo/Secunda" "useS (advS autem_Adv (pastS (simpleCl (useCNdefpl (useN Sabinus_N)) (transV habere_V2 (useCNindefpl (useN femina_N))))))"))
    , ($(tree "novo_modo/Secunda" "useS (advS autem_Adv (pastS (simpleCl (useCNdefpl (useN Romanus_N)) (complVA copula_VA (useA fallax_A)))))"))
    )
  , ( ($(tree "novo_modo/Secunda" "useS (advS autem_Adv (pastS (simpleCl (useCNdefpl (useN Romanus_N)) (complVA copula_VA (useA fallax_A)))))"))
    , ($(tree "novo_modo/Secunda" "useS (advS autem_Adv (pastS (simpleCl (useCNdefpl (useN Sabinus_N)) (transV habere_V2 (useCNindefpl (useN femina_N))))))"))
    )
  , ( ($(tree "novo_modo/Secunda" "useS (advS etiam_Adv (pastS (simpleCl (useCNdefpl (useN Sabinus_N)) (transV habere_V2 (useCNdefsg (useN religio_N))))))"))
    , ($(tree "novo_modo/Secunda" "useS (advS iam_Adv (pastS (simpleCl (useCNdefpl (useN Romanus_N)) (complVA copula_VA (useA victus_A)))))"))
    )
  , ( ($(tree "novo_modo/Secunda" "useS (advS iam_Adv (pastS (simpleCl (useCNdefpl (useN Romanus_N)) (complVA copula_VA (useA victus_A)))))"))
    , ($(tree "novo_modo/Secunda" "useS (advS etiam_Adv (pastS (simpleCl (useCNdefpl (useN Sabinus_N)) (transV habere_V2 (useCNdefsg (useN religio_N))))))"))
    )
  , ( ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (useCNdefpl (useN Sabinus_N)) (transV amare_V2 (useCNdefpl (useN liber_N)))))"))
    , ($(tree "novo_modo/Secunda" "useS (negPastS (simpleCl (usePron they_PP) (transV copula_V2 (useCNindefpl (attribCN (useA Romanus_A) (useN liber_N))))))"))
    )
  , ( ($(tree "novo_modo/Secunda" "useS (negPastS (simpleCl (useCNdefpl (useN iuvenis_N)) (transV copula_V2 (useCNindefpl (attribCN (useA Romanus_A) (useN liber_N))))))"))
    , ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (useCNdefpl (useN Sabinus_N)) (transV amare_V2 (useCNdefpl (useN liber_N)))))"))
    )
  , ( ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (useCNdefpl (useN Sabinus_N)) (transV amare_V2 (useCNdefpl (useN mulier_N)))))"))
    , ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (usePron they_PP) (transV copula_V2 (useCNindefpl (attribCN (useA Sabinus_A) (useN liber_N))))))"))
    )
  , ( ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (useCNdefpl (useN iuvenis_N)) (transV copula_V2 (useCNindefpl (attribCN (useA Sabinus_A) (useN liber_N))))))"))
    , ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (useCNdefpl (useN Sabinus_N)) (transV amare_V2 (useCNdefpl (useN mulier_N)))))"))
    )
  , ( ($(tree "novo_modo/Secunda" "useS (presS (simpleCl (useCNdefpl (useN Sabinus_N)) (transV dicere_V2 (useCNdefpl (attribCN (useA Romanus_A) (useN vir_N))))))"))
    , ($(tree "novo_modo/Secunda" "useS (presS (useVVCl (usePron they_PP) velle_VV (transV occidere_V2 (useCNdefpl (attribCN (useA Romanus_A) (useN vir_N))))))"))
    )
  , ( ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (useCNdefpl (useN Romanus_N)) (transV contendere_V2 (usePron they_PP))))"))
    , ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (usePron they_PP) (transV contendere_V2 (useCNdefpl (useN Romanus_N)))))"))
    )
  , ( ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (useCNdefpl (useN Romanus_N)) (transV docere_V2 (usePron they_PP))))"))
    , ($(tree "novo_modo/Secunda" "useS (pastS (simpleCl (usePron they_PP) (transV docere_V2 (useCNdefpl (useN Romanus_N)))))"))
    )
  ]
