concrete ExemplumRulesTest of ExemplumRules =
  ExemplumCatTest, TenseX-[Pol,Ant,TTAnt,PPos,PNeg,ASimul,AAnter,Adv,Utt] **
  open Prelude in {

lincat
  Pol, Ant = {s : Str} ;
  Utterance = {s : Str} ;

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

  useCl pol ant cl = {s = ant.s ++ pol.s ++ cl.s} ;
  useS s = s ;
  focusAdv adv s = {s = adv.s ++ s.s} ;

  
  PPos   = {s = []} ;
  PNeg   = {s = "not"} ;
  ASimul = {s = []} ;
  AAnter = {s = "has"} ;
}
