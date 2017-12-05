--# -path=/home/herb/src/foreign/GF/lib/src/english
concrete PrimaLexEng of PrimaLex = CatEng ** PrimaLexI with (Cat=CatEng), (Structural=StructuralEng), (Lexicon=LexiconEng) **open ParadigmsEng,
(D=DictEng), VerbEng, ResEng, Prelude in {
  lin
    imperium_N = D.empire_N ;
    Romanus_A = mkA "Roman" ;
    imperator_N = D.emperor_N ;
    civitas_N = D.society_N ;
    externus_A = D.foreign_A ;
    vincere_V2 = D.conquer_V2 ;
    victus_A = mkA "conquered" ;
    saepe_Adv = D.often_Adv;
    provincia_N = D.province_N ;
    devenire_V2 = D.become_V2 ;
    Gallia_PN = mkPN (mkN "Gaul") ;
    Africa_PN = D.africa_PN ;
    Germanus_N = mkN "Germanic" ;
    hostis_N = D.enemy_N ;
    dicere_V = D.say_V ;

    Augustus_PN = mkPN (mkN "Augustus") ;
    Caesar_N = mkN "Casear" ;

    laetus_A = D.happy_A ;
    anxius_A = mkA "troubled" ;
    felix_A = D.lucky_A ;
    coniux_N = D.wife_N ;
    sapiens_A = D.wise_A ;
    numen_N = D.divinity_N ;
    ingens_A = D.enormous_A ;
}