--# -path=prelude:abstract:common:api:scandinavian:swedish
concrete PrimaLexSwe of PrimaLex = CatSwe ** PrimaLexI
  with (Cat=CatSwe), (Structural=StructuralSwe), (Lexicon=LexiconSwe) **
  open ParadigmsSwe, (Irreg=IrregSwe), (Verb=VerbSwe), (Res=ResSwe), Prelude in {

lin  
  copula_VA = mkVA Res.verbBe ;
  copula_V2 = mkV2 Res.verbBe ;

  imperium_N = mkN "rike" "riket" "riken" "rikena" ;
  Romanus_A = mkA "romersk" ;
  imperator_N = mkN "imperator" "imperatorer" ;
  civitas_N = mkN "stat" "stater" ;
  externus_A = mkA "utländsk" ;
  vincere_V2 = mkV2 "besegrar" ;
  victus_A = mkA "besegrad" ;
  saepe_Adv = mkAdv "ofta" ;
  provincia_N = mkN "provins" "provinser" ;
  devenire_V2 = mkV2 (mkV "bli" "blir" "bli" "blev" "blivit" "bliven" "blivande") ;
  Gallia_PN = mkPN "Gallien" ;
  Africa_PN = mkPN "Afrika" ;
  Germanus_N = mkN "german" "germaner" ;
  hostis_N = mkN "fiende" "fiender" ;
  dicere_V = mkV "säga" "säger" "säg" "sade" "sagt" "sagd" ;

  Augustus_PN = mkPN "Augustus" ;
  Caesar_N = mkN "kejsare" "kejsare" ;

  laetus_A = mkA "glad" ;
  anxius_A = mkA "orolig" ;
  felix_A = mkA "lycklig" ;
  coniux_N = mkN "hustru" "hustrun" "hustrur" "hustrurna"  ;
  sapiens_A = mkA "vis" ;
  numen_N = mkN "gudom" "gudomar" ;
  ingens_A = mkA "enorm" ;

}