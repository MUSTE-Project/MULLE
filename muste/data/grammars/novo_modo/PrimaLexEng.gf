--# -path=prelude:abstract:common:api:english
concrete PrimaLexEng of PrimaLex = CatEng ** PrimaLexI
  with (Cat=CatEng), (Structural=StructuralEng), (Lexicon=LexiconEng) **
  open ParadigmsEng, (Irreg=IrregEng), (Verb=VerbEng), (Res=ResEng), Prelude in {

oper
  -- Note: The English RGL cannot encode the Copula as a regular verb, this is the best we can do:
  verbBe = mkV ("be"|"are") "is" "was" "been" "being" ;

lin
  copula_VA = mkVA verbBe ;
  copula_V2 = mkV2 verbBe ;

  imperium_N = mkN "empire" "empires" ;
  Romanus_A = mkA "Roman" ;
  imperator_N = mkN "imperator" ;
  civitas_N = mkN "society" "societies" ;
  externus_A = compoundA (mkA "foreign") ;
  vincere_V2 = mkV2 (mkV "conquer" "conquers" "conquered" "conquered" "conquering") ;
  victus_A = mkA "conquered" ;
  saepe_Adv = mkAdv "often" ;
  provincia_N = mkN "province" "provinces" ;
  devenire_V2 = mkV2 Irreg.become_V ;
  Gallia_PN = mkPN (mkN "Gaul") ;
  Africa_PN = mkPN "Africa" ;
  Germanus_N = mkN "German" ;
  hostis_N = mkN "enemy" "enemies" ;
  dicere_V = Irreg.say_V ;

  Augustus_PN = mkPN (mkN "Augustus") ;
  Caesar_N = mkN "emperor" ;

  laetus_A = mkA "happy" "happier" ;
  anxius_A = mkA "troubled" ;
  felix_A = mkA "lucky" "luckier" ;
  coniux_N = mkN feminine (mkN "wife" "wives") ;
  sapiens_A = mkA "wise" "wiser" ;
  numen_N = mkN "divinity" "divinities" ;
  ingens_A = compoundA (mkA "enormous") ;

}