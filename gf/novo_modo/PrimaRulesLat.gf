--# -path=latin-rgl/api:latin-rgl:.
concrete PrimaRulesLat of PrimaRules = CatLat ** PrimaRulesI
  with (Cat=CatLat), (Syntax=SyntaxLat), (Extra=ExtraLat), (Conjunction=ConjunctionLat) **
  open ResLat in {

lincat
  CS = Str ;

lin
  --    ppartAP v2 = PastPartAP (lin VP (mkVPSlash (lin V2 v2)));
  useS s = combineSentence s ! SPreO ! PreV ! SOV ;

}