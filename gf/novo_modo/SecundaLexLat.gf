--# -path=/home/herb/src/own/GF-latin/api:/home/herb/src/own/GF-latin:.
concrete SecundaLexLat of SecundaLex = CatLat ** SecundaLexI with (Cat=CatLat), (Structural=StructuralLat), (Lexicon=LexiconLat), (PrimaLex=PrimaLexLat) ** open ParadigmsLat, ExtraLat, (I=IrregLat), Prelude, ParamX, (R=ResLat) in {
  lin
    tectum_N = Lexicon.roof_N ;
    mons_N = Lexicon.mountain_N ;
    Romanus_N = mkN "Romanus" ;
    olim_Adv = mkAdv "olim" ;
    Palatinus_A = mkA "Palatinus" ;
    habitare_V2 = mkV2 (mkV "habitare" ) ;
    agricola_N = R.nounWithGender masculine ( mkN "agricola" ) ;
    humilis_A = mkA "humilis" "humilis" ;
    alius_A = mkA (mkN "alius") (mkN "alia") (mkN "aliud" "alius" neuter) ;
    quoque_Adv = mkAdv "quoque";
    populus_N = mkN "populus" ;
    Italia_PN = mkPN (mkN "Italia") ;
    colere_V2 = mkV2 ( mkV "colere" "colo" "colui" "cultum" ) ;
    Sabinus_N = mkN ( "Sabinus" | "Sabina" ) ;
    Etruscus_N = mkN "Etruscus" ;
    contendere_V2 = mkV2 ( mkV "contendere" "contendo" "contendi" "contentum" );
    quamquam_Adv = mkAdv "quamquam" ;
    Italicus_A = mkA "Italicus";
    tradere_V2 = mkV2 (mkV "tradere" "trado" "tradidi" "traditum" );
    auspicium_N = mkN "auspicium" ;
    observare_V2 = mkV2 (mkV "observare" );

    igitur_Adv = mkAdv "igitur" ;
    liber_N = pluralN (mkN "liber" "liberi" masculine);
    autem_Adv = mkAdv "autem" ;
    nolle_VV = mkVV I.not8want_V False ;
    facere_V = I.make_V ;
    fallax_A = mkA "fallax";
    festivitas_N = mkN "festivitas" "festivitatis" feminine ;
    praeparere_V2 = mkV2 (mkV "praeparere");
    Roma_PN = mkPN (mkN "Roma" );
    invitare_V2 = mkV2 (mkV "invitare");
    gaudere_V = mkV "gaudere" ; -- semi-deponent
    causa_N = mkN "causa" ;
    gaudium_N = mkN "gaudium";
    subito_Adv = mkAdv "subito" ;
    iuvenis_N = mkN "iuvenis" "iuvenis" masculine ; -- also feminine
    rapere_V2 = mkV2 (mkV "rapere" "rapio" "rapui" "raptum");
    terrere_V2 = mkV2 (mkV "terrere" ) ;
    aliquot_A = { s = \\_,_ => "aliquot" } ;
    mensis_N = mkN "mensis" "mensis" masculine;
    communis_A = mkA "communis";
    forsitan_Adv = mkAdv "forsitan" ;
    etiam_Adv = mkAdv "etiam" ;
    aliquis_Pron = let gen = feminine | masculine in { pers = { s = \\_,_,c => StructuralLat.someSg_Det.s ! gen ! c  ; g = gen ; n = Sg } ; poss = {s = \\_,_ => "" } ; p = P3 } ;
    iterum_Adv = mkAdv "iterum" ;
    occidere_V2 = mkV2 (mkV "occidere" "occido" "occidi" "occasum");
    portare_V2 = mkV2 (mkV "portare") ;
    manere_V = mkV "manere" ;
    vidua_N = mkN "vidua" ;
    orbus_A = mkA "orbus" ;
    unus_A = mkA "unus" ;
    domus_N = Lexicon.house_N ;
    
    comma_Conj = mkConj "" "," Pl R.Comma ;
}