--# -path=latin-rgl
concrete ExemplumLexLat of ExemplumLex = CatLat ** ExemplumLexI
  with (Cat=CatLat), (Grammar=GrammarLat), (Lexicon=LexiconLat) **
  open ParadigmsLat, (Extra=ExtraLat), (Irreg=IrregLat), Prelude in {

lin

  copula_V = mkV2 Irreg.be_V ;

  hic_Adv = mkAdv "hic" ; 
  passim_Adv = mkAdv "passim" ; 

  imperium_N = mkN "imperium" ;
  Romanus_A = mkA "Romanus" False;
  imperator_N = mkN "imperator" "imperatoris" masculine ;
  civitas_N = mkN "civitas" "civitatis" feminine ;
  externus_A = mkA "externus" ;    
  vincere_V = Lexicon.win_V2 ;
  victus_A = mkA "victus" ;
  saepe_Adv = mkAdv "saepe" ; 
  provincia_N = mkN "provincia" ;    
  devenire_V = mkV2 (mkV "devenire") Extra.Nom_Prep;    
  Gallia_PN = mkPN (mkN "Gallia") ;
  Africa_PN = mkPN (mkN "Africa") ;
  Germanus_N = mkN "Germanus" ;
  hostis_N = mkN "hostis" "hostis" masculine ;
  dicere_V = mkV2 (mkV "dicere" "dico" "dixi" "dictum") ;

  Augustus_PN = mkPN (mkN "Augustus") ;
  Caesar_N = (mkN "Caesar" "Caesaris" masculine) ;

  laetus_A = mkA "laetus" ;
  anxius_A = mkA "anxius" ;
  felix_A = mkA "felix" "felicis" ;
  coniux_N = mkN "coniux" "coniugis" feminine ;
  sapiens_A = mkA "sapiens" "sapientis" ;
  numen_N = mkN "numen" "numinis" neuter ;
  ingens_A = mkA "ingens" "ingentis" ;

}
