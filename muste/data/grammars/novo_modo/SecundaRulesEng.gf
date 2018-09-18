concrete SecundaRulesEng of SecundaRules = CatEng ** SecundaRulesI
  with (Syntax=SyntaxEng), (PrimaRules=PrimaRulesEng) **
  open (R=ResEng), Prelude, ParamX in {

lincat CS = SS ;

lin
  impS pron vp =
    { s = let tmp = ( mkImp vp ).s ! R.CPos in
	    case pron.a of {
	      R.AgP1 n => tmp ! ImpF n True ;
	      R.AgP2 n => tmp ! ImpF n True ;
	      R.AgP3Sg _ =>  tmp ! ImpF Sg True ;
	      R.AgP3Pl _ =>  tmp ! ImpF Pl True
	    }
    }; -- lin S ({ s = pron.s ! R.npNom ++ vp.s ! R.VInf } ) ;
  --    useV2 v2 = let v = lin V { s = v2.s ; p = v2.p ; isRefl = v2.isRefl } in mkVP v ;
  useVV vv = lin VP (R.predVV (lin VV vv)) ;
  --    useS _ _ s = s ;
  useS s = s ;
  --    locNP np1 np2 = lin NP (mkNP (lin NP np1) (mkAdv on_Prep np2));

}