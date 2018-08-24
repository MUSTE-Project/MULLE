incomplete concrete ExemplumRulesI of ExemplumRules = Cat **
  open Grammar, Prelude in {

lin

  useN = UseN ;
  attribCN = AdjCN ;
  apposCN cn pn = ApposCN cn (UsePN pn) ;

  usePN = UsePN ;
  usePron = UsePron ;
  detCN = DetCN ;
  advNP = AdvNP ;
  conjNP conj np1 np2 = ConjNP conj (BaseNP np1 np2) ;

  useA = PositA ;

  prepNP = PrepNP ;

  intransV = UseV ;
  transV v2 np = ComplSlash (SlashV2a v2) np ;
  complVA = ComplVA ;
  advVP = AdvVP ;

  simpleCl = PredVP ;

  useCl cl = UseCl (TTAnt TPres ASimul) PPos cl ;
  useS = UttS ;
  focusAdv adv s = UttS (AdvS adv s) ;

}
