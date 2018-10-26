--# -path=prelude:abstract:common:api
incomplete concrete SecundaLexI of SecundaLex = Cat **
  open Structural, Lexicon, PrimaLex in {

lin
  copula_VA = PrimaLex.copula_VA ;
  copula_V2 = PrimaLex.copula_V2 ;

  terra_N = Lexicon.country_N ;
  et_Conj = Structural.and_Conj ;
  cum_Prep = Structural.with_Prep ;
  -- is_Pron = Structural.they_Pron ;
  vincere_V2 = PrimaLex.vincere_V2 ;
  victus_A = PrimaLex.victus_A ;
  multus_Det = PrimaLex.multus_Det ;
  docere_V2 = Lexicon.teach_V2 ;
  religio_N = Lexicon.religion_N ;

  vetus_A = Lexicon.old_A ;
  femina_N = Lexicon.woman_N ;
  non_Predet = Structural.not_Predet ;
  nullus_Quant = Structural.no_Quant ;
  sed_Adv = Structural.but_PConj ;
  dare_V3 = Lexicon.give_V3 ;
  pulcher_A = Lexicon.beautiful_A ;
  velle_VV = Structural.want_VV ;
  iam_Adv = Lexicon.already_Adv ;
  maritus_N = Lexicon.husband_N ;
  rex_N = Lexicon.king_N ;
  mulier_N = Lexicon.wife_N ;
  venire_V = Lexicon.come_V ;
  sine_Prep = Structural.without_Prep ;
  vertere_V = Lexicon.turn_V ;
  vir_N = Lexicon.man_N ;
  annus_N = Lexicon.year_N ;
  amare_V2 = Lexicon.love_V2 ;
  post_Prep = Structural.after_Prep ;
  
  they_PP = Structural.they_Pron ;
  habere_V2 = Structural.have_V2 ;
  magnus_A = Lexicon.big_A ;
  nos_PP = Structural.we_Pron ;

}