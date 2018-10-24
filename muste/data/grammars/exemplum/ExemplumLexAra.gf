--# -path=prelude:abstract:common:arabic
concrete ExemplumLexAra of ExemplumLex = ExemplumCatAra **
  ExemplumLexI - [john_PN,or_Conj,today_Adv]
  with (Cat=CatAra), (Grammar=GrammarAra), (Lexicon=LexiconAra) **
  open ParadigmsAra, ResAra, Prelude in {
    
lin

  copula_V = dirV2 (v1hollow {f = "ك"; c = "و" ; l = "ن"} u) ;

  john_PN = mkPN " يوحنا " ;
  today_Adv = Lexicon.now_Adv ;
  or_Conj = Grammar.and_Conj ;

}
