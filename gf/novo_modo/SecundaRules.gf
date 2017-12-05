abstract SecundaRules = Cat ** {
  cat CS ;
  fun
    useA : A -> AP ;
    attribNP : NP -> NP -> Cl ;
    simpleCl : NP -> VP -> Cl ;
    infCL : NP -> VV -> VP -> Cl ;
    usePron : Pron -> NP ;
    useCNdefsg : CN -> NP ;
    --    useCNpl : CN -> NP ;
    useNdefpl : N -> NP ;
    useNindefpl : N -> NP ;
    usePN : PN -> NP ;
    possNP : NP -> NP -> NP ;
    useN : N -> CN ;
    attribCN : AP -> CN -> CN ;
    -- apposCN : CN -> NP -> CN ;
    pastS : Cl -> S ;
    presS : Cl -> S ;
    negPastS : Cl -> S ;
    impS : Pron -> VP -> S ;
    advS : Adv -> S -> S ;
    conjNP : Conj -> NP -> NP -> NP ;
    conjS : Conj -> S -> S -> S ;
    advVP : Adv -> VP -> VP ;
    advVP2 : Adv -> VP -> VP ;
--    advCN : Adv -> CN -> CN ;
    intransV : V -> VP ;
    transV : V2 -> NP -> VP ;
    complA : A -> VP ;
--    complN : N -> VP ;
    complCN : CN -> VP ;
    prepNP : Prep -> NP -> Adv ;
    useV2 : V2 -> VP ;
    useVV : VV -> VP ;
    useS : S -> CS ;
}