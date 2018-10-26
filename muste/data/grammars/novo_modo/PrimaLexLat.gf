--# -path=prelude:abstract:common:latin-rgl/api:api:latin-rgl
concrete PrimaLexLat of PrimaLex = CatLat ** PrimaLexI
  with (Cat=CatLat), (Structural=StructuralLat), (Lexicon=LexiconLat) **
  open ParadigmsLat, ExtraLat, (I=IrregLat), Prelude, ParamX in {

lin
  copula_VA = mkVA I.be_V ;
  copula_V2 = mkV2 I.be_V Nom_Prep ;

  imperium_N = mkN "imperium" ;
  Romanus_A = mkA "Romanus" False;
  imperator_N = mkN "imperator" "imperatoris" masculine ;
  civitas_N = mkN "civitas" "civitatis" feminine ;
  externus_A = mkA "externus" ;    
  vincere_V2 = Lexicon.win_V2 ;
  victus_A = mkA "victus" ;
  saepe_Adv = mkAdv "saepe" ;    
  provincia_N = mkN "provincia" ;    
  devenire_V2 = mkV2 (mkV "devenire") Nom_Prep;    
  Gallia_PN = mkPN (mkN "Gallia") ;
  Africa_PN = mkPN (mkN "Africa") ;
  Germanus_N = mkN "Germanus" ;
  hostis_N = mkN "hostis" "hostis" masculine ;
  dicere_V = mkV "dicere" "dico" "dixi" "dictum" ;

  Augustus_PN = mkPN (mkN "Augustus") ;
  Caesar_N = (mkN "Caesar" "Caesaris" masculine) ;

  laetus_A = mkA "laetus" ;
  anxius_A = mkA "anxius" ;
  felix_A = mkA "felix" "felicis" ;
  coniux_N = mkN "coniux" "coniugis" feminine ;
  sapiens_A = mkA "sapiens" "sapientis" ;
  numen_N = mkN "numen" "numinis" neuter ;
  ingens_A = mkA "ingens" "ingentis" ;
  -- he_PP = let pron = Structural.he_Pron in ({p = P3 ; pers = { s = table { PronDrop => \\_,_ => "(Pers.pron 3rd pers. Sg.)" ; PronNonDrop => pron.pers.s ! PronNonDrop } ; g = masculine ; n = Sg } ; poss = pron.poss } | pron );

}