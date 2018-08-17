incomplete concrete ExemplumRulesI of ExemplumRules = Cat **
  open Grammar, Prelude in {

lin

  useA a = PositA a ;

  useN n = UseN n ;
  attribCN ap cn = AdjCN ap cn ;
  apposCN cn pn = ApposCN cn (UsePN pn) ;

  usePN pn = UsePN pn ;
  usePron pron = UsePron pron ;
  detCN det cn = DetCN det cn ;
  conjNP conj np1 np2 = ConjNP conj (BaseNP np1 np2) ;

  intransV v2 = UseV v2 ;
  transV v2 np = ComplSlash (SlashV2a v2) np ;
  complVA v2 ap = ComplVA v2 ap ;
  advVP adv vp = AdvVP vp adv ;
  adVVP adV vp = AdVVP adV vp ;

  simpleCl np vp = PredVP np vp ;

  useCl cl = UseCl (TTAnt TPres ASimul) PPos cl ;
  useS s = UttS s ;
  focusAdv adv s = UttS (AdvS adv s) ;
  focusAdV adv s = UttS (AdvS adv s) ;

}
