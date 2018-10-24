--# -path=prelude:abstract:common:api:scandinavian:swedish
concrete PrimaRulesSwe of PrimaRules = CatSwe ** PrimaRulesI
  with (Cat=CatSwe), (Syntax=SyntaxSwe), (Conjunction=ConjunctionSwe) **
  open PhraseSwe, ResSwe, Prelude in {

lincat CS = SS ;

lin
  useS s = UttS s ;

}