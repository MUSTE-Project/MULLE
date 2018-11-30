--# -path=prelude:abstract:common:latin-rgl/api:api:latin-rgl
concrete SecundaRulesLat of SecundaRules = CatLat ** SecundaRulesI
  with (Cat=CatLat),(Syntax=SyntaxLat),(PrimaRules=PrimaRulesLat)  ** open ExtraLat,ResLat,Prelude,TenseX in {
lincat
  CS = SS ;
lin

  impS pron vp = lin S {
    s = \\_ =>
      pron.pers.s ! PronDrop ! PronNonRefl ! Nom ++
      vp.imp ! (VImp1 pron.pers.n) ++
      vp.obj ++
      vp.compl ! Ag pron.pers.g pron.pers.n Acc ++ vp.adv ;
    neg =  \\_ => [] ; o = \\_ => [] ; v = \\_ => [] ;
    p = PPos ;
    t = TPres ;
    sadv = []
    } ;

  -- useV2 v2 = let v = lin V { act = v2.act ; imp = v2.imp; inf = v2.inf ; pass = v2.pass } in lin VP (mkVP v) ;

  -- just using (mkVP (lin V vv)) yields an error, this is a workaround:
  useVV vv =
    let vv2v : VV -> V = \vv' -> lin V vv'
    in lin VP (mkVP (vv2v vv)) ;

  useS s = lin CS {s = combineSentence s ! SPreS ! PreV ! SOV} ;
  -- these are the possible options for
  -- the (sentence) adverb position and sentence order:
  -- ! (SPreS | SPreV | SPreO | SPreNeg)
  -- ! (PreS | PreV | PreO | PreNeg | InV | InS)
  -- ! SOV

  -- locNP np1 np2 = lin NP (mkNP (lin NP np1) (lin Adv { s = np2.preap.s ! Ag np2.g np2.n Gen ++ np2.adv.s ++ np2.s ! Gen ++ np2.postap.s ! Ag np2.g np2.n Gen } ));
  -- useNPCS np = np.preap.s ! Ag np.g np.n Nom ++ np.adv.s ++ np.s ! Nom ++ np.postap.s ! Ag np.g np.n Nom ;
  -- conjCS conj cs1 cs2 = conj.s1 ++ cs1 ++ conj.s2 ++ cs2 ;

};