--# -path=prelude:abstract:common
incomplete concrete ExemplumRulesI of ExemplumRules = Cat, Tense **
  open Grammar, Prelude in {

lincat
  Utterance = {s : Str} ;

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

  useCl pol ant cl = UseCl (TTAnt TPres ant) pol cl ;
  useS s = lin Utterance (UttS s) ;
  focusAdv adv s = lin Utterance (UttS (AdvS adv s)) ;

}
