incomplete concrete SecundaRulesI of SecundaRules = Cat ** open Syntax,Extra,PrimaRules in {
  lin
    useA = PrimaRules.useA ;
    attribNP np1 np2 = lin Cl (mkCl (lin NP np1) (lin NP np2)) ;
    simpleCl = PrimaRules.simpleCl ;
    infCl np vv vp = lin Cl (mkCl (lin NP np) (lin VV vv) (lin VP vp));
    usePron = PrimaRules.usePron ;
    useCNdefsg = PrimaRules.useCNdefsg ;
    --    useCNpl cn = lin NP (mkNP aPl_Det (lin CN cn));
    useN = PrimaRules.useN ;
    attribCN = PrimaRules.attribCN ;
    useNdefpl n = lin NP (mkNP thePl_Det (lin N n) ) ;
    useNindefpl n = lin NP (mkNP aPl_Det (lin N n) );
    usePN = PrimaRules.usePN ;
    possNP np1 np2 = lin NP (mkNP (lin NP np1) (lin Adv (mkAdv possess_Prep (lin NP np2)))) ;
    pastS cl = lin S (mkS (mkTemp pastTense simultaneousAnt) positivePol (lin Cl cl) ) ;
    negPastS cl = lin S (mkS (mkTemp pastTense simultaneousAnt) negativePol (lin Cl cl) ) ;
    presS cl = lin S (mkS (mkTemp presentTense simultaneousAnt) positivePol (lin Cl cl) ) ;
    advS = PrimaRules.advS ;
    conjNP conj np1 np2 = lin NP (mkNP (lin Conj conj) (lin NP np1) (lin NP np2)) ;
--    conjS conj s1 s2 = lin S (mkS (lin Conj conj) (lin S s1) (lin S s2)) ;
    advVP adv vp = lin VP (mkVP (lin Adv adv) (lin VP vp) ) ;
    advVP2 adv vp = lin VP (mkVP (lin VP vp) (lin Adv adv) ) ;
--    apposCN cn np = lin CN (mkCN (lin CN cn) (lin NP np)) ;
--    advCN adv cn = lin CN (mkCN (lin CN cn) (lin Adv adv )) ;
    intransV = PrimaRules.intransV ;
    transV = PrimaRules.transV ;
    complA = PrimaRules.complA ;
    --    complN n = lin VP (mkVP (lin N n)) ;
    complCN cn = lin VP (mkVP (lin CN cn)) ;
    prepNP prep np = lin Adv (mkAdv (lin Prep prep) (lin NP np) ) ;
}