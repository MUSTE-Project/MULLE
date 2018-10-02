concrete ExemplumRulesTest of ExemplumRules = ExemplumCatTest ** open Prelude in {

lin
  useN n = n ;
  attribCN ap n = {s = ap.s ++ BIND ++ n.s} ;
  apposCN cn pn = {s = cn.s ++ pn.s} ;

  usePN pn = pn ;
  usePron pron = pron ;
  detCN det cn = {s = det.s ++ cn.s} ;
  advNP np adv = {s = np.s ++ adv.s} ;
  conjNP conj np1 np2 = {s = np1.s ++ conj.s ++ np2.s} ;

  useA a = a ;

  prepNP prep np = {s = prep.s ++ np.s} ;

  intransV v = v ;
  transV v np = {s = v.s ++ np.s} ;
  complVA v ap = {s = v.s ++ ap.s} ;
  advVP vp adv = {s = vp.s ++ adv.s} ;

  simpleCl np vp = {s = np.s ++ vp.s} ;

  useCl cl = cl ;
  useS s = s ;
  focusAdv adv s = {s = adv.s ++ s.s} ;
}
