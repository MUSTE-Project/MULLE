concrete ExemplumLexAra of ExemplumLex = ExemplumCatAra **
  ExemplumLexI - [john_PN,or_Conj,today_Adv,it_Pron,he_Pron,she_Pron,they_Pron]
  with (Cat=CatAra), (Grammar=GrammarAra), (Lexicon=LexiconAra) **
  open ParadigmsAra, ResAra, Prelude in {
    
lin

  copula_V = dirV2 (v1hollow {f = "ك"; c = "و" ; l = "ن"} u) ;

  john_PN = mkPN " يوحنا " ;
  today_Adv = Lexicon.now_Adv ;
  or_Conj = Grammar.and_Conj ;

  it_Pron = mkPronX "ِت" "ِت" "ِتس" (Per3 Fem Sg) ;
  he_Pron = mkPronX "هُوَ" "هُ" "هُ" (Per3 Masc Sg) ;
  she_Pron = mkPronX "هِيَ" "ها" "ها" (Per3 Fem Sg) ;
  they_Pron = mkPronX "هُمْ" "هُمْ" "هُمْ" (Per3 Masc Pl) ; 

oper

  mkPronX : (_,_,_ : Str) -> PerGenNum -> NP = \ana,nI,I,pgn ->
    { s = 
        table {
          Nom => ana;
          Acc => nI;
          Gen => I
        };
      a = {pgn = pgn; isPron = False };
      lock_NP = <>
    };

}
