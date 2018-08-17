concrete SecundaLexSwe of SecundaLex = CatSwe ** SecundaLexI
  with (Structural=StructuralSwe), (Lexicon=LexiconSwe), (PrimaLex=PrimaLexSwe) **
  open ParadigmsSwe, (I=IrregSwe), (D=DictSwe), Prelude, NumeralSwe in {

lin
  Romanus_N = D.romare_nn_1_N ;
  Romanus_A = D.romansk_av_1_A ;
  mons_N = Lexicon.hill_N ;
  olim_Adv = D.fordom_ab_1_Adv ;
  tectum_N = Lexicon.house_N ;
  Palatinus_A = mkA "palatinsk" ;
  habitare_V2 = mkV2 D.bo_vb_1_V ;
  agricola_N = D.bonde_nn_1_N ;
  humilis_A = D.laag_av_1_1_A ;
  alius_N = mkN "annan" ;
  quoque_Adv = D.aeven_ab_1_1_Adv ;
  populus_N = D.folk_nn_1_N ;
  Italia_PN = mkPN "Italien" ;
  colere_V2 = mkV2 D.odla_vb_1_V ;
  Sabinus_N = mkN "sabinare" "sabinaren" "sabinar" "sabinarna" ;
  Sabinus_A = mkA "sabinsk" ;
  Etruscus_N = mkN "etrusk" "etrusken" "etrusker" "etruskerna" ;
  contendere_V2 = mkV2 D.sammandrabba_vb_1_V ;
  quamquam_Adv = mkAdv "fastän" ;
  Italicus_A = mkA "italisk";
  tradere_V2 = mkV2 D.oeverlaemna_vb_1_1_V ;
  auspicium_N = D.omen_nn_1_N ;
  observare_V2 = mkV2 D.iaktta_vb_1_V ;

  igitur_Adv = D.alltsaa_ab_1_1_Adv ;
  liber_N = Lexicon.child_N ;
  autem_Adv = Structural.but_PConj ;
  nolle_VV = mkVV D.vaegra_vb_1_1_V ;
  facere_V = D.goera_vb_1_1_V ;
  fallax_A = D.svekfull_av_1_A ;
  festivitas_N = D.festlighet_nn_1_N ;
  praeparere_V2 = mkV2 D.foerbereda_vb_1_1_V ;
  Roma_PN = mkPN "Rom" ;
  invitare_V2 = mkV2 (I.inbjuda_V) ;
  gaudere_V = mkV "glädjas" ;
  causa_N = D.orsak_nn_1_N ;
  gaudium_N = mkN "glädje" utrum ;
  subito_Adv = mkAdv "plötsligt" ;
  iuvenis_N = D.ungdom_nn_1_N ;
  rapere_V2 = mkV2 D.roeva_vb_1_1_V ;
  terrere_V2 = mkV2 (mkV "skrämmar") ;
  domus_N = D.hem_nn_1_N ;
  --    aliquot_A = mkAdv "några" ;
  mensis_N = D.maanad_nn_1_1_N ;
  communis_A = D.gemensam_av_1_A ;
  forsitan_Adv = D.kanske_ab_1_Adv ;
  etiam_Adv = D.aeven_ab_1_1_Adv ;
  --    aliquis_Pron = Structural.someSg_Det ;
  iterum_Adv = D.aater_ab_1_1_Adv ;
  occidere_V2 = Lexicon.kill_V2 ;
  portare_V2 = mkV2 D.baera_vb_1_1_V ;
  manere_V = D.foerbli_vb_1_1_V ;
  vidua_N = D.aenka_nn_1_1_N ;
  orbus_A = D.foeraeldraloes_av_1_1_A ;
  --    unus_A = pot01 ;

  comma_Conj =  mkConj "" "," plural ;
  on_Prep = StructuralSwe.on_Prep;

oper 
  mkConj = overload {
    mkConj : Str -> Conj 
	  = \s -> lin Conj {s1 = [] ; s2 = s ; n = plural ; isDiscont = False} ;
    mkConj : Str -> Str -> Number -> Conj 
	  = \x,y,n -> lin Conj {s1 = x ; s2 = y ; n = n ; isDiscont = False} ;
    mkConj : Str -> Str -> Number -> Bool -> Conj 
	  = \x,y,n,d -> lin Conj {s1 = x ; s2 = y ; n = n ; isDiscont = d} ;
    } ;

}