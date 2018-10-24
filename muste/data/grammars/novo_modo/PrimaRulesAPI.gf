--# -path=prelude:abstract:common:api
concrete PrimaRulesAPI of PrimaRules = open Prelude in {
  lincat
    S, AP, Cl, NP, CN, VP, CS, ListNP = SS ;
  lin
    useA a = ss ("(mkAP " ++ a.s ++ ")") ;
    simpleCl np vp = ss ("(mkCl " ++ np.s ++ " " ++ vp.s ++ ")") ;
    usePN pn = ss ("(mkNP " ++ pn.s ++ ")") ;
    usePron pron = ss ("(mkNP " ++ pron.s ++ ")") ;
    useCNdefsg cn = ss ("(mkNP theSg_Det " ++ cn.s ++ ")") ;
    useCNindefsg cn = ss ("(mkNP aSg_Det " ++ cn.s ++ ")") ;
    useCNindefpl cn = ss ("(mkNP aPl_Det " ++ cn.s ++ ")") ;
    complexNP det cn = ss ("(mkNP " ++ det.s ++ " " ++ cn.s ++ ")") ;
    conjNP np1 np2 = ss ("(mkListNP " ++ np1.s ++" " ++ np2.s ++ ")") ;
    extConjNP lnp np = ss ("(mkListNP " ++ np.s ++ " " ++ lnp.s ++ ")") ;
    useConjNP conj lnp = ss ("(mkNP " ++ conj.s ++ " " ++ lnp.s ++ ")") ;
    useN n = ss ("(mkCN " ++ n.s ++ ")") ;
    attribCN ap cn = ss ("(mkCN " ++ ap.s ++ " " ++ cn.s ++ ")") ;
    apposCNdefsg cn pn = ss ("(mkNP theSg_Det (mkCN " ++ cn.s ++ ") (mkNP " ++ pn.s ++ "))") ;
    useCl cl = ss ("(mkS (mkTemp presentTense simultaneousAnt) positivePol " ++ cl.s ++ ")") ;
    advS adv s = ss ("(mkS " ++ adv.s ++ " " ++ s.s ++ ")") ;
    intransV v = ss ("(mkVP " ++ v.s ++ ")") ;
    transV v2 np = ss ("(mkVP " ++ v2.s ++ " " ++ np.s ++ ")") ;
    complVA va ap = ss ("(mkVP " ++ va.s ++" " ++ ap.s ++ ")") ;
    --    useS s = lin Utt (mkUtt (lin S s)) ;
    --    ppartAP v2 = PastPartAP (lin VP (mkVPSlash (lin V2 v2)));
    useS s = ss ("(combineSentence " ++ s.s ++ " ! SPreO ! PreV ! SOV)") ;
}