--# -path=latin-rgl/api:latin-rgl:.
concrete PrimaLexAPI of PrimaLex = open Prelude in{
  lincat PN, N, A, V2, VA, V, Adv, Conj, Pron, Det = SS ;
  lin
    -- LexI
    magnus_A = ss "big_A" ;
    habere_V2 = ss "have_V2" ;
    multus_Det = ss "many_Det" ;
    
    he_PP = ss "he_Pron" ;
    
    puella_N = ss "girl_N" ;
    amicus_N = ss "friend_N" ;
    vinum_N = ss "wine_N" ;
    bonus_A = ss "good_A" ;
    pater_N = ss "father_N2" ;
    and_Conj = ss "and_Conj" ;
    -- LexLat
    copula_VA = ss "copula_VA" ;
    copula_V2 = ss "copula_V2" ;
    
    tenere_V2 = ss "tenere_V2" ;
    imperium_N = ss "imperium_N" ;
    Romanus_A = ss "Romanus_A" ;
    imperator_N = ss "imperator_N" ;
    civitas_N = ss "civitas_N" ;
    externus_A = ss "externus_A" ;
    vincere_V2 = ss "vincere_V2" ;
    victus_A = ss "victus_A" ;
    saepe_Adv = ss "saepe_Adv" ;
    provincia_N = ss "provincia_N" ;
    devenire_V2 = ss "devenire_V2";
    Gallia_PN = ss "Gallia_PN" ;
    Africa_PN = ss "Africa_PN" ;
    Germanus_N = ss "Germanus_N" ;
    hostis_N = ss "hostis_N" ;
    dicere_V = ss "dicere_V";
    
    Augustus_PN = ss "Augustus_PN" ;
    Caesar_N = ss "Caesar_N" ;
    
    laetus_A = ss "laetus_A" ;
    anxius_A = ss "anxius_A" ;
    felix_A = ss "felix_A" ;
    coniux_N = ss "coniux_N" ;
    sapiens_A = ss "sapiens_A";
    numen_N = ss "numen_N" ;
    ingens_A = ss "ingens_A" ;
}