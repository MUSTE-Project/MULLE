abstract TertiaRules = Cat ** {
  cat CS ;
  fun
    -- Prima
    useA : A -> AP ;
    useN : N -> CN ;
    usePN : PN -> NP ;
    useCNdefsg : CN -> NP ;
    attribCN : AP -> CN -> CN ;
    complCN : CN -> VP ;
    simpleCl : NP -> VP -> Cl ;
    useCl : Cl -> S ;
    useS : S -> CS ;
    -- Tertia
    useSsvo : S -> CS ;
    uttNP : NP -> CS ;
}