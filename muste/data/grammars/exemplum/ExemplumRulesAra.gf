--# -path=prelude:abstract:common:arabic
concrete ExemplumRulesAra of ExemplumRules =
  CatAra, TenseX-[Utt] **
  ExemplumRulesI-[useS,focusAdv,conjNP,complVA]
  with (Cat=CatAra), (Conjunction=ConjunctionAra), (Grammar=GrammarAra) **
  open ParadigmsAra, (Res=ResAra), Prelude in {

lin
  useS s = s ;
  focusAdv adv s = {s = adv.s ++ s.s} ;
  complVA = ComplVAx ;
  -- conjNP not implemented yet

oper

  -- This is a hack since ComplVA is not implemented in the RGL yet
  ComplVAx : Res.Verb2 -> AP -> VP ;
  ComplVAx v ap = Res.insertObj (ap2np ap) (Res.predVSlash v) ;

  ap2np : AP -> NP ;
  ap2np ap = lin NP {s = \\cas => ap.s ! Res.NoHum ! Res.Fem ! Res.Sg ! Res.Indef ! cas;
                     a = {pgn = Res.Per3 Res.Fem Res.Sg; isPron = False}};

}
