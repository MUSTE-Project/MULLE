abstract ExemplumRules = Cat ** {

fun

  useN : N -> CN ;
  attribCN : AP -> CN -> CN ;
  apposCN : CN -> PN -> CN ;

  usePN : PN -> NP ;
  usePron : Pron -> NP ;
  detCN : Det -> CN -> NP ;
  advNP : NP -> Adv -> NP ;
  conjNP : Conj -> NP -> NP -> NP ;

  useA : A -> AP ;

  prepNP : Prep -> NP -> Adv ; 

  intransV : V2 -> VP ;
  transV : V2 -> NP -> VP ;
  complVA : V2 -> AP -> VP ;
  advVP : VP -> Adv -> VP ;

  simpleCl : NP -> VP -> Cl ;

  useCl : Cl -> S ;
  useS : S -> Utt ;
  focusAdv : Adv -> S -> Utt ;

}
