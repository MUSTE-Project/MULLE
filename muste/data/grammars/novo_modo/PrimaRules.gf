abstract PrimaRules = Cat, Conjunction ** {

cat CS ;

fun
  useA : A -> AP ;
  --    ppartAP : V2 -> AP ;
  simpleCl : NP -> VP -> Cl ;
  usePN : PN -> NP ;
  usePron : Pron -> NP ;
  useCNdefsg : CN -> NP ;
  useCNindefsg : CN -> NP ;
  useCNindefpl : CN -> NP ;
  complexNP : Det -> CN -> NP ;
  conjNP : NP -> NP -> ListNP ;
  extConjNP : ListNP -> NP -> ListNP ;
  useConjNP : Conj -> ListNP -> NP ;
  useN : N -> CN ;
  attribCN : AP -> CN -> CN ;
  apposCNdefsg : CN -> PN -> NP ;
  useCl : Cl -> S ;
  advS : Adv -> S -> S ;
  intransV : V -> VP ;
  transV : V2 -> NP -> VP ;
  complVA : VA -> AP -> VP ;
  useS : S -> CS ;

}