abstract SecundaRules = Cat ** { -- , Conjunction ** {
  cat CS ;
  fun
    useA : A -> AP ; -- Prima
    simpleCl : NP -> VP -> Cl ; -- Prima
--    usePN : PN -> NP ; -- Prima -- not used yet
    usePron : Pron -> NP ; -- Prima
    useCNdefsg : CN -> NP ; -- Prima
    useCNindefpl : CN -> NP ; -- Prima?
--    conjNP : NP -> NP -> ListNP ; -- Prima -- not used yet
--    extConjNP : ListNP -> NP -> ListNP ; -- Prima -- not used yet
--    useConjNP : Conj -> ListNP -> NP ; -- Prima -- not used yet
    useN : N -> CN ; -- Prima
    attribCN : AP -> CN -> CN ; -- Prima
    advS : Adv -> S -> S ; -- Prima
    intransV : V -> VP ; -- Prima
    transV : V2 -> NP -> VP ; -- Prima
    complVA : VA -> AP -> VP ; -- Prima
    --    useS : SAdvPos -> AdvPos -> S -> CS ; -- Prima
    useS : S -> CS ; -- Prima

    -- nolite
    impS : Pron -> VP -> S ;
    -- gaudent
    presS : Cl -> S ;
    pastS : Cl -> S ;
    negPastS : Cl -> S ;

    
    useCNdefpl : CN -> NP ;
--    prepNP : NP -> Prep -> NP -> NP ; -- not used yet

    advNP : Adv -> NP -> NP ;
    
    -- Obs: Hacky for sentence 4, not really working?
--    useNPCS : NP -> CS ; -- not used yet
--    conjCS : Conj -> CS -> CS -> CS ; -- not used yet

    useVVCl : NP -> VV -> VP -> Cl ;
--     attribNP : NP -> NP -> Cl ;
--     infCL : NP -> VV -> VP -> Cl ;

--     possNP : NP -> NP -> NP ; -- not used yet
--     locNP : NP -> NP -> NP ;

--     -- apposCN : CN -> NP -> CN ;

--     conjS : Conj -> S -> S -> S ;
--     advVP : Adv -> VP -> VP ;
--     advVP2 : Adv -> VP -> VP ;
-- --    advCN : Adv -> CN -> CN ;


-- --    complN : N -> VP ;
--     complCN : CN -> VP ;

--     useV2 : V2 -> VP ;
    useVV : VV -> VP ;


}
      