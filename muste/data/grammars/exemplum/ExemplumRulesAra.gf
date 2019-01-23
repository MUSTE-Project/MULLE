concrete ExemplumRulesAra of ExemplumRules =
  CatAra, TenseX-[Utt] **
  ExemplumRulesI-[useS,focusAdv]
  with (Cat=CatAra), (Conjunction=ConjunctionAra), (Grammar=GrammarAra) **
  open (Res=ResAra), Prelude in {

lin
  useS s = uttS s ;
  focusAdv adv s = uttS (AdvS adv s) ;

oper
  uttS : S -> Utterance = \s -> lin Utterance {s = s.s ! Res.Verbal} ;

}
