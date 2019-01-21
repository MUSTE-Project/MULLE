--# -path=prelude:abstract:common:arabic
concrete ExemplumLexAra of ExemplumLex = CatAra **
  ExemplumLexI - [john_PN,today_Adv]
  with (Cat=CatAra), (Grammar=GrammarAra), (Lexicon=LexiconAra) **
  open ParadigmsAra, ResAra, Prelude in {
    
lin

  copula_V = dirV2 (Res.v1hollow {f = "ك"; c = "و" ; l = "ن"} Res.u) ;

  john_PN = mkPN " يوحنا " ;
  today_Adv = Lexicon.now_Adv ;

}
