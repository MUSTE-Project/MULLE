--# -path=prelude:abstract:common:chinese
concrete ExemplumRulesChi of ExemplumRules = CatChi, TenseChi ** ExemplumRulesI
  with (Cat=CatChi), (Conjunction=ConjunctionChi), (Grammar=GrammarChi) ;
