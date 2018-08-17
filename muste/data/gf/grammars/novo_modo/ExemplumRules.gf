abstract ExemplumRules = Cat ** {

fun

  useA : A -> AP ;

  useN : N -> CN ;
  attribCN : AP -> CN -> CN ;
  apposCN : CN -> PN -> CN ;

  usePN : PN -> NP ;
  usePron : Pron -> NP ;
  detCN : Det -> CN -> NP ;
  conjNP : Conj -> NP -> NP -> NP ;

  intransV : V2 -> VP ;
  transV : V2 -> NP -> VP ;
  complVA : V2 -> AP -> VP ;
  advVP : Adv -> VP -> VP ;
  adVVP : AdV -> VP -> VP ;

  simpleCl : NP -> VP -> Cl ;

  useCl : Cl -> S ;
  useS : S -> Utt ;
  focusAdv : Adv -> S -> Utt ;
  focusAdV : AdV -> S -> Utt ;

}
