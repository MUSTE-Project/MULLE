concrete ExemplumLexSwe of ExemplumLex = CatSwe ** ExemplumLexI
  with (Cat=CatSwe), (Grammar=GrammarSwe), (Lexicon=LexiconSwe) **
  open ParadigmsSwe, (Irreg=IrregSwe), (Res=ResSwe), Prelude in {

lin  

  copula_V = mkV2 Res.verbBe ;

  hic_Adv = mkAdv "här" ; 
  passim_Adv = mkAdv "överallt" ; 

  imperium_N = mkN "rike" ; 
  Romanus_A = mkA "romersk" ;
  imperator_N = mkN "imperator" "imperatorer" ;
  civitas_N = mkN "stat" "stater" ;
  externus_A = mkA "utländsk" ;
  vincere_V = mkV2 "besegrar" ;
  victus_A = mkA "besegrad" ;
  saepe_Adv = mkAdV "ofta" ;
  provincia_N = mkN "provins" "provinser" ;
  devenire_V = mkV2 (Irreg.bliva_V) ;
  Gallia_PN = mkPN "Gallien" ;
  Africa_PN = mkPN "Afrika" ;
  Germanus_N = mkN "german" "germaner" ;
  hostis_N = mkN "fiende" "fiender" ;
  dicere_V = mkV2 Irreg.säga_V ;

  Augustus_PN = mkPN "Augustus" ;
  Caesar_N = mkN "kejsare" "kejsare" ;

  laetus_A = mkA "glad" ;
  anxius_A = mkA "orolig" ;
  felix_A = mkA "lycklig" ;
  coniux_N = mkN "hustru" "hustrun" "hustrur" "hustrurna"  ;
  sapiens_A = mkA "vis" ;
  numen_N = mkN "gudom" ; 
  ingens_A = mkA "enorm" ;

}