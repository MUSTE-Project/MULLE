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
      ss ("(mkNP " ++ np1.s ++ " (mkAdv " ++ prep.s ++ np2.s ++ ") )");
    pastS cl = ss ("(mkS (mkTemp pastTense simultaneousAnt) positivePol" ++ cl.s ++ ")") ;
    negPastS cl = ss ("(mkS (mkTemp pastTense simultaneousAnt) negativePol" ++ cl.s ++")") ;
    advNP a np = ss ("(mkNP" ++ np.s ++ a.s ++ ")") ;
    useVVCl np vv vp = ss ("(mkCl" ++ np.s ++ vv.s ++ vp.s ++ ")") ;
    useVV vv = ss ("(let v = lin V { act = vv.act ; imp = vv.imp; inf = vv.inf ; pass = vv.pass } in " ++ vv.s ++ ")")  ;
    useS s = ss ("(combineSentence " ++ s.s ++ " ! (SPreS | SPreV | SPreO | SPreNeg) ! (PreS | PreV | PreO | PreNeg | InV | InS) ! SOV)") ;
    impS pron vp = ss ("((\\pron,vp -> lin S {s = \\_ => pron.pers.s ! PronDrop ! PronNonRefl ! Nom ++ vp.imp ! (VImp1 pron.pers.n) ; neg =  \\_ => [] ; o = \\_ => [] ; v = \\_ => [] ; p = { s = [] ; p = Pos } ; t = { s = [] ; t = Pres } ; sadv = { s = [] } } ;)" ++ pron.s ++ vp.s ++ ")") ;
}