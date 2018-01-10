--# -path=/home/herb/src/foreign/GF/lib/src/english
concrete TertiaRulesEng of TertiaRules = CatEng ** TertiaRulesI with (Cat=CatEng),(Syntax=SyntaxEng),(PrimaRules=PrimaRulesEng) ** open (R=ResEng), Prelude, ParamX in {
}