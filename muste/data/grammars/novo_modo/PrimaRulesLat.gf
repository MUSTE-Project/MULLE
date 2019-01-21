--# -path=prelude:abstract:common:api:latin
concrete PrimaRulesLat of PrimaRules = CatLat ** PrimaRulesI
  with (Cat=CatLat), (Syntax=SyntaxLat), (Conjunction=ConjunctionLat) **
  open ResLat, Prelude in {

lincat CS = SS ;

lin
  --    ppartAP v2 = PastPartAP (lin VP (mkVPSlash (lin V2 v2)));
  useS s = ss (combineSentence s ! SPreO ! PreV ! SOV) ;

}
