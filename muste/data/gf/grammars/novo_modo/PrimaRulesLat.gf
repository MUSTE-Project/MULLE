--# -path=latin-rgl/api:latin-rgl:.
concrete PrimaRulesLat of PrimaRules = CatLat ** PrimaRulesI-[useCNdefsg,useCNindefsg,useCNindefpl]
  with (Cat=CatLat), (Syntax=SyntaxLat), (Conjunction=ConjunctionLat) **
  open ResLat in {

lincat
  CS = Str ;

lin
  useCNdefsg cn = let q : Det = lin Det {s = \\_,_ => "" ; sp = \\_,_ => "(definite)" ; n = Sg } in lin NP (mkNP (q | theSg_Det) (lin CN cn)) ;
  useCNindefsg cn = let q : Det = lin Det {s = \\_,_ => "" ; sp = \\_,_ => "(indefinite)" ; n = Sg } in lin NP (mkNP (q | aSg_Det) (lin CN cn)) ;
  useCNindefpl cn = let q : Det = lin Det {s = \\_,_ => "" ; sp = \\_,_ => "(indefinite)" ; n = Pl } in lin NP (mkNP (q | aPl_Det) (lin CN cn));
  --    ppartAP v2 = PastPartAP (lin VP (mkVPSlash (lin V2 v2)));
  useS s = combineSentence s ! SPreO ! PreV ! SOV ;

}