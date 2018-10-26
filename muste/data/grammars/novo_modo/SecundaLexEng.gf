--# -path=prelude:abstract:common:api:english
concrete SecundaLexEng of SecundaLex = CatEng ** SecundaLexI
  with (Structural=StructuralEng), (Lexicon=LexiconEng), (PrimaLex=PrimaLexEng) **
  open ParadigmsEng, (I=IrregEng), (D=DictEng), Prelude in {

lin
  Romanus_N = mkN "Roman" ;
  Romanus_A = mkA "Roman" ;
  mons_N = Lexicon.hill_N ;
  olim_Adv = D.once_Adv ;
  tectum_N = Lexicon.house_N ;
  Palatinus_A = mkA "Palatine" ;
  habitare_V2 = mkV2 D.live_in_V ;
  agricola_N = D.farmer_N ;
  humilis_A = D.low_A ;
  alius_A = D.other_A ;
  quoque_Adv = D.also_Adv ;
  populus_N = D.people_N ;
  Italia_PN = D.italy_PN ;
  colere_V2 = D.cultivate_V2 ;
  Sabinus_N = mkN "Sabine" ;
  Sabinus_A = mkA "Sabinus" ;
  Etruscus_N = mkN "Etruscan" ;
  contendere_V2 = lin V2 ( D.contend_VS ** { c2 = [] ; isRefl = False }) ;
  quamquam_Adv = D.though_Adv ;
  Italicus_A = mkA "Italic";
  tradere_V2 = D.hand_over_V2 ;
  auspicium_N = D.divination_N ;
  observare_V2 = D.observe_V2 ;

  igitur_Adv = D.therefore_Adv ;
  liber_N = Lexicon.child_N ;
  autem_Adv = Structural.but_PConj ;
  nolle_VV = D.refuse_VV ;
  facere_V = I.make_V ;
  fallax_A = D.deceitful_A ;
  festivitas_N = D.festival_N ;
  praeparare_V2 = D.prepare_V2 ;
  Roma_PN = D.rome_PN ;
  invitare_V2 = D.invite_V2 ;
  gaudere_V = D.rejoice_V ;
  causa_N = D.cause_N ;
  gaudium_N = D.joy_N;
  subito_Adv = mkAdv "suddenly" ;
  iuvenis_N = D.youth_N ;
  rapere_V2 = D.abduct_V2 ;
  terrere_V2 = D.frighten_V2 ;
  domus_N = D.home_N ;
  aliquot_A = D.some_A ;
  mensis_N = D.month_N ;
  communis_A = D.public_A ;
  forsitan_Adv = D.perhaps_Adv ;
  etiam_Adv = D.even_Adv ;
  aliquis_Pron = lin Pron ( D.someone_NP ** { sp = \\_ => "" } ) ;
  iterum_Adv = D.again_Adv ;
  occidere_V2 = Lexicon.kill_V2 ;
  portare_V2 = D.carry_V2 ;
  manere_V = D.stay_V ;
  vidua_N = D.widow_N ;
  orbus_A = mkA "orphaned" ;
  unus_A = mkA "one" ;

  comma_Conj =  mkConj "," plural ;
  colon_Conj =  mkConj ":" plural ;
  on_Prep = StructuralEng.on_Prep ;
  dicere_V2 = mkV2 Lexicon.say_VS ;

}