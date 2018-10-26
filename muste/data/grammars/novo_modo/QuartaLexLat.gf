--# -path=prelude:abstract:common:latin-rgl/api:api:latin-rgl
concrete QuartaLexLat of QuartaLex = CatLat ** QuartaLexI with (Cat=CatLat),(Structural=StructuralLat),(Lexicon=LexiconLat),(SecundaLex=SecundaLexLat),(TertiaLex=TertiaLexLat),(Syntax=SyntaxLat) ** open ParadigmsLat, Prelude, ResLat in {
  lin
    hic_Pron = { pers = { s = \\_,_,c => StructuralLat.this_Quant.s ! Ag Masc Sg c ; g = Masc ; n = Sg }; poss = { s = \\_,_ => [] } ; p = P3 } ;
    dividere_V = mkV "dividere" "divido" "divisi" "divisum" ;
    divisus_A = mkA "divisus" ;
    pars_N = mkN "pars" "partis" feminine ;
    qui_Pron = { pers = { s = \\_,_,c => StructuralLat.which_IQuant.s ! Ag Masc Sg c ; g = Masc ; n = Sg }; poss = { s = \\_,_ => [] } ; p = P3 } ;
    incolere_V2 = mkV2 ( mkV "incolere" "incolo" "incolui" nonExist ) ; -- active forms only
    Belgae_N = mkN "Belga" ;
    Aquitani_N = mkN "Aquitanus" ;
    ipse_Pron = { pers = { s = \\_,_ => table Case [ "ipse" ; "ipsum" ; "ipsius" ; "ipsi" ; "ipso" ; "ipse" ] ; g = Masc ; n = Sg }; poss = { s = \\_,_ => [] } ; p = P3 } ;
    omnis_Pron = { pers = { s = \\_,_,c => Structural.every_Det.s ! Masc ! c ; g = Masc ; n = Pl }; poss = { s = \\_,_ => [] } ; p = P3 } ;
    Celtae_N = mkN "Caelta" ;
    Gallus_N = mkN "Gallus" ;
    appellare_V = mkV "appelare" ;
    ab_Prep = mkPrep ( "a" | "ab" )  Abl ; -- ab before vowel
    Garunna_PN = mkPN ( mkN "Garunna" ) ;
    flumen_N = mkN "flumen" "fluminis" neuter ;
    Matrona_PN = mkPN ( mkN "Matrona" ) ;
    Sequana_PN = mkPN ( mkN "Sequana" ) ;
    fortis_A = mkA "fortis" "fortis" ;
    reliquus_A = mkA "reliquus" ;
    virtus_N = mkN "virtus" "virtutis" feminine ;
    praecedere_V2 = mkV2 ( mkV "praecedere" "praecedo" "praecessi" "praecessum" ) ; 
}