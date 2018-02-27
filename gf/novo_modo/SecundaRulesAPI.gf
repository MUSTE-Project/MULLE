concrete SecundaRulesAPI of SecundaRules = SecundaLexAPI ** open Prelude, PrimaRulesAPI in {
  lincat
    S, CN, VP, NP, Cl, AP, CS = SS;
  lin
    -- Prima
    useA = PrimaRulesAPI.useA ;
    simpleCl = PrimaRulesAPI.simpleCl ;
    usePN = PrimaRulesAPI.usePN ;
    usePron = PrimaRulesAPI.usePron ;
    useCNdefsg = PrimaRulesAPI.useCNdefsg ;
    useCNindefpl = PrimaRulesAPI.useCNindefpl ;
--    conjNP conj np1 np2 = lin NP (mkNP (lin Conj conj) (lin NP np1) (lin NP np2)) ;
    conjNP = PrimaRulesAPI.conjNP ;
    useN = PrimaRulesAPI.useN ;
    attribCN = PrimaRulesAPI.attribCN ;
    advS = PrimaRulesAPI.advS ;
    intransV = PrimaRulesAPI.intransV ;
    transV = PrimaRulesAPI.transV ;
    complVA = PrimaRulesAPI.complVA ;
    presS = PrimaRulesAPI.useCl;

    -- Secunda
    useCNdefpl cn = ss ("mkNP thePl_Det " ++ cn.s ++ ")") ;
    prepNP np1 prep np2 =
      ss ("(mkNP " ++ np1.s ++ " (mkAdv " ++ prep.s ++ " " ++ np2.s ++ ") )");
    pastS cl = ss ("(mkS (mkTemp pastTense simultaneousAnt) positivePol " ++ cl.s ++ ")") ;
--     attribNP np1 np2 = lin Cl (mkCl (lin NP np1) (lin NP np2)) ;

--     infCl np vv vp = lin Cl (mkCl (lin NP np) (lin VV vv) (lin VP vp));

--     --    useCNpl cn = lin NP (mkNP aPl_Det (lin CN cn));


--     useNdefpl n = lin NP (mkNP thePl_Det (lin N n) ) ;
--     useNindefpl n = lin NP (mkNP aPl_Det (lin N n) );

--     possNP np1 np2 = lin NP (mkNP (lin NP np1) (lin Adv (mkAdv possess_Prep (lin NP np2)))) ;

--     negPastS cl = lin S (mkS (mkTemp pastTense simultaneousAnt) negativePol (lin Cl cl) ) ;
-- --    presS cl = lin S (mkS (mkTemp presentTense simultaneousAnt) positivePol (lin Cl cl) ) ;


-- --    conjS conj s1 s2 = lin S (mkS (lin Conj conj) (lin S s1) (lin S s2)) ;
--     advVP adv vp = lin VP (mkVP (lin Adv adv) (lin VP vp) ) ;
--     advVP2 adv vp = lin VP (mkVP (lin VP vp) (lin Adv adv) ) ;
-- --    apposCN cn np = lin CN (mkCN (lin CN cn) (lin NP np)) ;
--     advCN adv cn = lin CN (mkCN (lin CN cn) (lin Adv adv )) ;

--     --    complN n = lin VP (mkVP (lin N n)) ;
--     complCN cn = lin VP (mkVP (lin CN cn)) ;

}