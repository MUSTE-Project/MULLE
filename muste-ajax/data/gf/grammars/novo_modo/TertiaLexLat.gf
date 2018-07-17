--# -path=latin-rgl/api:latin-rgl:.
concrete TertiaLexLat of TertiaLex = CatLat ** TertiaLexI with (Cat=CatLat),(Structural=StructuralLat),(Lexicon=LexiconLat),(PrimaLex=PrimaLexLat),(SecundaLex=SecundaLexLat) ** open ParadigmsLat,ResLat in {
  lin
    -- p41
    antiquus_A = mkA "antiquus" ;
    Sicilia_PN = mkPN (mkN "Sicilia" ) ;
    insula_N = mkN "insula" ;
    Britannia_PN = mkPN ( mkN "Britannia" ) ;
    Germania_PN = mkPN ( mkN "Germania" ) ;
    Suecia_PN = mkPN ( mkN "Suecia" ) ;
    paeninsula_N = mkN "paeninsula" ;
    Hispania_PN = mkPN ( mkN "Hispania" ) ;
    Graecia_PN = mkPN ( mkN "Graecia" ) ;
    Britannus_N = mkN "Britannus" ;
    Suecus_N = mkN "Suecus" ;

    -- p42
    neque_Conj = mkConj "neque" "neque" Sg Neither ; -- ???
    
    -- -- p43
    gerere_V2 = mkV2 (mkV "gerere" "gero" "gessi" "gessum" ) ;
    bulla_N = mkN "bulla" ;
    curare_V = mkV "curare" ;
    quod_Conj = mkConj "" "quod" Sg Because ; -- ???
    defendere_V = mkV "defendere" "defondo" "defendi" "defensum" ;
    serva_N = mkN "serva" ;
    matrona_N = mkN "matrona" ;
    stola_N = mkN "stola" ;
    filia_N = mkN "filia" ;
    
    -- -- p44
    delectare_V = mkV "delectare" ;
    fabula_N = mkN "fabula" ;
    narrare_V = mkV "narrare" ;
    audire_V = mkV "audire" ; -- 4
    fortasse_Adv = mkAdv "fortasse" ;

    -- -- p45
    servus_N = mkN "servus" ;
    pomum_N = mkN "pomum" ;
    itaque_Adv = mkAdv "itaque" ; -- Conj?
    calathus_N = mkN "calathus" ;
    putridus_A = mkA "putridus" ;
    donum_N = mkN "donum" ;
    omnis_A = { s = \\_ => table { Ag g n c => Structural.every_Det.s ! g ! c } } ;  -- Det?
    diligenter_Adv = mkAdv "diligenter" ;
    maculare_V2 = mkV2 ( mkV "maculare" ) ;
    mox_Adv = mkAdv "mox" ;
    cunctus_A = mkA "cunctus" ;
    tristis_A = mkA "tristis" "tristis" ;
    certe_Adv = mkAdv "certe" ;
}
 