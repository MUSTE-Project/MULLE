--# -path=latin-rgl/api:latin-rgl:.
concrete QuartaRulesLat of QuartaRules = CatLat ** QuartaRulesI with (Cat=CatLat),(Syntax=SyntaxLat),(PrimaRules=PrimaRulesLat)  ** open ExtraLat,ResLat in {
}