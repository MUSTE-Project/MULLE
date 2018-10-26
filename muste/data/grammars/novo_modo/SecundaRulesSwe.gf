--# -path=prelude:abstract:common:api:scandinavian:swedish
concrete SecundaRulesSwe of SecundaRules = CatSwe ** SecundaRulesI
  with (Syntax=SyntaxSwe), (PrimaRules=PrimaRulesSwe) ** open (R=ResSwe), Prelude, ParamX, CommonScand in {
  lincat CS = SS ;
  lin
    impS pron vp =
      let imp = mkImp vp
      in lin S { s = \\_ => imp.s ! Pos ! pron.a.n } ;
      -- }; -- lin S ({ s = pron.s ! R.npNom ++ vp.s ! R.VInf } ) ;
    -- useV2 v2 = let v = lin V { s = v2.s ; p = v2.p ; isRefl = v2.isRefl } in mkVP v ;
    useVV vv = let v = { s = vv.s ; part = vv.part ; vtype = vv.vtype } in lin VP (mkVP (lin V v)) ;
    --useS _ _ s = ss (s.s ! Main ) ;
    useS s = ss (s.s ! Main ) ;
    -- locNP np1 np2 = lin NP (mkNP (lin NP np1) (mkAdv on_Prep np2));
};