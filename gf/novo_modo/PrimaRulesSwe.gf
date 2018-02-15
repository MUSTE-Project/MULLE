concrete PrimaRulesSwe of PrimaRules = CatSwe ** PrimaRulesI
  with (Cat=CatSwe), (Syntax=SyntaxSwe), (Extra=ExtraSwe), (Phrase=PhraseSwe), (Conjunction=ConjunctionSwe) **
  open ResSwe, Prelude in {

lincat CS = SS ;

lin
  useS s = Phrase.UttS s ;

}