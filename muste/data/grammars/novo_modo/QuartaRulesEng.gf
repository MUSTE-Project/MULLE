--# -path=prelude:abstract:common:api:english
concrete QuartaRulesEng of QuartaRules = CatEng ** QuartaRulesI with (Cat=CatEng),(Syntax=SyntaxEng),(PrimaRules=PrimaRulesEng) ** open (R=ResEng), Prelude, ParamX in {
  lincat CS = SS ;
}