concrete PrimaLexSwe of PrimaLex = CatSwe ** PrimaLexI
  with (Cat=CatSwe), (Structural=StructuralSwe), (Lexicon=LexiconSwe) **
  open ParadigmsSwe, (Verb=VerbSwe), (Res=ResSwe), Prelude in {

lin  
  copula_VA = mkVA Res.verbBe ;
  copula_V2 = mkV2 Res.verbBe ;

  imperium_N = mkN "imperie" "imperiet" "imperier" "imperierna" ;
  Romanus_A = mkA "romersk" ;
  imperator_N = mkN "härskare" "härskare" ;
  civitas_N = mkN "samhälle" ;
  externus_A = mkA "främmande" ;
  vincere_V2 = mkV2 "erövra" ;
  victus_A = mkA "erövrad" ;
  saepe_Adv = mkAdv "ofta" ;
  provincia_N = mkN "provins" "provinser" ;
  devenire_V2 = mkV2 (mkV "bli" "blir" "bli" "blev" "blivit" "bliven" "blivande") ;
  Gallia_PN = mkPN "Gallien" ;
  Africa_PN = mkPN "Afrika" ;
  Germanus_N = mkN "tysk" ;
  hostis_N = mkN "fiende" "fiender" ;
  dicere_V = mkV "säga" "säger" "säg" "sade" "sagt" "sagd" ;

  Augustus_PN = mkPN "Augustus" ;
  Caesar_N = mkN "kejsare" "kejsare" ;

  laetus_A = mkA "glad" ;
  anxius_A = mkA "ängslig" ;
  felix_A = mkA "lyckosam" "lyckosamt" "lyckosamma" "lyckosammare" "lyckosammast" ;
  coniux_N = mkN "hustru" "hustrun" "hustrur" "hustrurna"  ;
  sapiens_A = mkA "vis" ;
  numen_N = mkN "gudomlighet" "gudomligheter" ;
  ingens_A = mkA "enorm" ;

}