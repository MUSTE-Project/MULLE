--# -path=/home/herb/src/foreign/GF/lib/src/english
concrete TertiaLexEng of TertiaLex = CatEng ** TertiaLexI with (Cat=CatEng),(Structural=StructuralEng),(Lexicon=LexiconEng),(PrimaLex=PrimaLexEng),(SecundaLex=SecundaLexEng) ** open ParadigmsEng,(D=DictEng) in {
  lin
    -- p41
    antiquus_A = D.ancient_A ;
    Sicilia_PN = mkPN "Sicily" ;
    insula_N = D.island_N ;
    Britannia_PN = mkPN "Britain" ;
    Germania_PN = mkPN "Germanic empire" ;
    Suecia_PN = D.sweden_PN ;
    paeninsula_N = D.peninsula_N ;
    Hispania_PN = D.spain_PN ;
    Graecia_PN = D.greece_PN ;
    Britannus_N = mkN "Briton" ;
    Suecus_N = D.swedeMasc_N ;

    -- p42
    neque_Conj = D.neither7nor_DConj ;
    
    -- -- p43
    gerere_V2 = D.wear_V2 ;
    bulla_N = D.amulet_N ; -- "bulla"
    curare_V = prepV2 (partV (mkV "take") "care") (mkPrep "of") ; 
    quod_Conj = mkConj "" "because" ; -- correct?
    defendere_V = D.protect_V ;
    serva_N = D.slave_N ;
    matrona_N = D.woman_N ;
    stola_N = mkN "stola" ;
    filia_N = D.daughter_N ;
    
    -- -- p44
    delectare_V = D.please_V ;
    fabula_N = D.story_N ;
    narrare_V = D.tell_V2 ;
    audire_V = D.listen_V ; -- 4
    fortasse_Adv = D.perhaps_Adv ;

    -- -- p45
    servus_N = D.slave_N ;
    pomum_N = D.fruit_N ;
    itaque_Adv = D.therefore_Adv ; -- Conj?
    calathus_N = D.basket_N ;
    putridus_A = D.rotten_A ;
    donum_N = D.gift_N ;
    diligenter_Adv = mkAdv "carefully" ;
    maculare_V2 = D.stain_V2 ;
    mox_Adv = D.soon_Adv ;
    cunctus_A = D.all_A ;
    tristis_A = D.sad_A ;
    certe_Adv = mkAdv "surely" ;
}