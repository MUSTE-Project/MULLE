--# -path=latin-rgl/api:latin-rgl:.
concrete SecundaRulesLat of SecundaRules = CatLat ** SecundaRulesI with (Cat=CatLat),(Syntax=SyntaxLat),(PrimaRules=PrimaRulesLat)  ** open ExtraLat,ResLat in {
  lincat CS = Str ;
  lin
    impS pron vp =
  lin S {
	s = \\_ => pron.pers.s ! PronDrop ! PronNonRefl ! Nom ++ vp.imp ! (VImp1 pron.pers.n) ;
	neg =  \\_ => [] ; o = \\_ => [] ; v = \\_ => [] ;
	p = lin Pol { s = [] ; p = Pos } ;
	t = lin Tense { s = [] ; t = Pres } ;
	sadv = { s = [] } 
	} ;
    useV2 v2 = let v = lin V { act = v2.act ; imp = v2.imp; inf = v2.inf ; pass = v2.pass } in lin VP (mkVP v) ;
    useVV vv = let v = lin V { act = vv.act ; imp = vv.imp; inf = vv.inf ; pass = vv.pass } in lin VP (mkVP v) ;
    useS s = combineSentence s ! PreO ! SOV ;
};