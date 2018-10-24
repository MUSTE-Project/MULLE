--# -path=prelude:abstract:common:latin-rgl/api:api:latin-rgl
concrete TertiaRulesLat of TertiaRules = CatLat ** TertiaRulesI with (Cat=CatLat),(Syntax=SyntaxLat),(PrimaRules=PrimaRulesLat)  ** open ExtraLat,ResLat in {
  lincat CS = Str ;
  lin
    useS s = combineSentence s ! PreO ! SOV ;
    useSsvo s = combineSentence s ! PreO ! SVO ;
}