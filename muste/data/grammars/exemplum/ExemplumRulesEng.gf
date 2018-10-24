--# -path=prelude:abstract:common:english
concrete ExemplumRulesEng of ExemplumRules =
  CatEng, TenseX-[Pol,PPos,PNeg,SC,CAdv] ** ExemplumRulesI
  with (Cat=CatEng), (Conjunction=ConjunctionEng), (Grammar=GrammarEng) **
  open ResEng, Prelude in {

lin
  PPos = {s = [] ; p = CPos} ;
  PNeg = {s = [] ; p = CNeg True} ; -- contracted: don't

}
