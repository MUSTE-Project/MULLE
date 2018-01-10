concrete PrimaLexEng of PrimaLex = CatEng ** PrimaLexI
  with (Cat=CatEng), (Structural=StructuralEng), (Lexicon=LexiconEng) **
  open ParadigmsEng, (Irreg=IrregEng), (Verb=VerbEng), (Res=ResEng), Prelude in {

lin
  imperium_N = mkN "empire" "empires" ;
  Romanus_A = mkA "Roman" ;
  imperator_N = mkN "emperor" "emperors" ;
  civitas_N = mkN "society" "societies" ;
  externus_A = compoundA (mkA "foreign") ;
  vincere_V2 = mkV2 (mkV "conquer" "conquers" "conquered" "conquered" "conquering") ;
  victus_A = mkA "conquered" ;
  saepe_Adv = mkAdv "often" ;
  provincia_N = mkN "province" "provinces" ;
  devenire_V2 = mkV2 Irreg.become_V ;
  Gallia_PN = mkPN (mkN "Gaul") ;
  Africa_PN = mkPN "Africa" ;
  Germanus_N = mkN "Germanic" ;
  hostis_N = mkN "enemy" "enemies" ;
  dicere_V = Irreg.say_V ;

  Augustus_PN = mkPN (mkN "Augustus") ;
  Caesar_N = mkN "Casear" ;

  laetus_A = mkA "happy" "happier" ;
  anxius_A = mkA "troubled" ;
  felix_A = mkA "lucky" "luckier" ;
  coniux_N = mkN feminine (mkN "wife" "wives") ;
  sapiens_A = mkA "wise" "wiser" ;
  numen_N = mkN "divinity" "divinities" ;
  ingens_A = compoundA (mkA "enormous") ;

}
