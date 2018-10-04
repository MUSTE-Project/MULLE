concrete ExemplumRulesAra of ExemplumRules =
  ExemplumCatAra, TenseX-[Utt] **
  ExemplumRulesI-[useCl,useS,focusAdv,conjNP,complVA,apposCN]
  with (Cat=CatAra), (Conjunction=ConjunctionAra), (Grammar=GrammarAra) **
  open ParadigmsAra, ResAra, Prelude in {

lin
  useS s = s ;
  focusAdv adv s = {s = adv.s ++ s.s} ;
  apposCN cn pn = ApposCNx cn (UsePN pn) ;
  complVA = ComplVAx ;

  -- this is a real hack: transforming Simul/Anter to Pres/Past
  useCl pol ant cl = 
    {s = pol.s ++ ant.s ++ case ant.a of {
       ASimul => cl.s ! ResAra.Pres ! pol.p ! Verbal ;
       AAnter => cl.s ! ResAra.Past ! pol.p ! Verbal
       }} ;

oper

  ApposCNx : CN -> NP -> CN ;
  ApposCNx cn np = lin CN {s = cn.s; g = cn.g; h = cn.h;
                           adj = \\num,stat,cas => cn.adj!num!stat!cas ++ np.s!cas} ;

  ComplVAx : VA -> AP -> VP ;
  ComplVAx v ap = insertObj (ap2np ap) (predV v) ;

  ap2np : AP -> NP ;
  ap2np ap = lin NP {s = \\cas => ap.s ! NoHum ! Fem ! Sg ! Indef ! cas;
                     a = {pgn = Per3 Fem Sg; isPron = False}};

}
