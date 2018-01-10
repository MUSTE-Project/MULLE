abstract PrimaRules = Cat ** {

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
  conjNP : NP -> NP -> NP ;
  useN : N -> CN ;
  attribCN : AP -> CN -> CN ;
  apposCNdefsg : CN -> NP -> NP ;
  useCl : Cl -> S ;
  advS : Adv -> S -> S ;
  intransV : V -> VP ;
  transV : V2 -> NP -> VP ;
  complA : A -> VP ;
  complCN : CN -> VP ;
  useS : S -> CS ;

}