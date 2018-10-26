--# -path=prelude:abstract:common:api:english
concrete QuartaLexEng of QuartaLex = CatEng ** QuartaLexI with (Cat=CatEng),(Structural=StructuralEng),(Lexicon=LexiconEng),(PrimaLex=PrimaLexEng),(SecundaLex=SecundaLexEng),(TertiaLex=TertiaLexEng),(Syntax=SyntaxEng) ** open ParadigmsEng,(D=DictEng),ParamX,Prelude,ResEng in {
  lin
    hic_Pron = { s = \\c => StructuralEng.this_Quant.sp ! True ! Sg ! c ; a = AgP3Sg Masc ; sp = \\_ => [] };
    dividere_V = D.divide_V ;
    divisus_A = mkA "divided" ;
    pars_N = D.part_N ;
    qui_Pron = lin Pron ( { s = StructuralEng.whoSg_IP.s ; a = AgP3Sg Masc ; sp = \\_ => [] } ) ;
    incolere_V2 = D.inhabit_V2 ;
    Belgae_N = mkN "Belgae" "Belgae" ;
    Aquitani_N = mkN "Aquitan" ;
    ipse_Pron = let refl = reflPron in { s = \\c => refl ! AgP3Sg Masc ; a = AgP3Sg Masc ; sp = \\_ => [] } ;
    omnis_Pron = { s = \\_ => Structural.every_Det.s ; a = AgP3Pl Masc ; sp = \\_ => [] } ;
    Celtae_N = mkN "Celt" ;
    Gallus_N = mkN "Gaul" ;
    appellare_V = D.call_V ;
    ab_Prep = from_Prep ;
    Garunna_PN = mkPN "Garonne" ;
    flumen_N = D.river_N ;
    Matrona_PN = mkPN "Marne" ;
    Sequana_PN = mkPN "Seine" ;
    fortis_A = D.strong_A ;
    reliquus_A = mkA "reliquus" ;
    virtus_N = D.virtue_N ;
    praecedere_V2 = D.surpass_V2 ;
}