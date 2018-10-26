--# -path=prelude:abstract:common:api:english
concrete TertiaRulesEng of TertiaRules = CatEng ** TertiaRulesI with (Cat=CatEng),(Syntax=SyntaxEng),(PrimaRules=PrimaRulesEng) ** open (R=ResEng), Prelude, ParamX in {
}