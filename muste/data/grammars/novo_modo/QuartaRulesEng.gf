--# -path=/home/herb/src/foreign/GF/lib/src/english
concrete QuartaRulesEng of QuartaRules = CatEng ** QuartaRulesI with (Cat=CatEng),(Syntax=SyntaxEng),(PrimaRules=PrimaRulesEng) ** open (R=ResEng), Prelude, ParamX in {
  lincat CS = SS ;
}