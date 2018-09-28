concrete ExemplumRulesAra of ExemplumRules = ExemplumCatAra **
  ExemplumRulesI - [useS,focusAdv,conjNP,complVA,apposCN]
  with (Cat=CatAra), (Conjunction=ConjunctionAra), (Grammar=GrammarAra) **
  open ParadigmsAra, ResAra, Prelude in {

lin
  useS s = s ;
  focusAdv adv s = {s = adv.s ++ s.s} ;
  apposCN cn pn = ApposCNx cn (UsePN pn) ;
  complVA = ComplVAx ;

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
