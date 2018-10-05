--# -path=latin-rgl/api:latin-rgl:.
concrete SecundaRulesLat of SecundaRules = CatLat ** SecundaRulesI
  with (Cat=CatLat),(Syntax=SyntaxLat),(PrimaRules=PrimaRulesLat)  ** open ExtraLat,ResLat,Prelude in {
lincat
  CS = SS ;
lin

  -- impS pron vp = lin S {
  --   s = \\_ => pron.pers.s ! PronDrop ! PronNonRefl ! Nom ++ vp.imp ! (VImp1 pron.pers.n) ++ vp.obj ++ vp.compl ! Ag pron.pers.g pron.pers.n Acc ++ vp.adv ;
  --   neg =  \\_ => [] ; o = \\_ => [] ; v = \\_ => [] ;
  --   p = lin Pol { s = [] ; p = Pos } ;
  --   t = lin Tense { s = [] ; t = Pres } ;
  --   sadv = { s = [] } 
  --   } ;

  --    useV2 v2 = let v = lin V { act = v2.act ; imp = v2.imp; inf = v2.inf ; pass = v2.pass } in lin VP (mkVP v) ;
  useVV vv = let v = lin V { act = vv.act ; imp = vv.imp; inf = vv.inf ; pass = vv.pass } in lin VP (mkVP v) ;
  --    useS s = combineSentence s ! SPreO ! PreV ! SOV ;
  --    useS sadv adv s = sadv.s ++ adv.s ++ combineSentence s ! sadv.pos ! adv.pos ! SOV ;
  --    useS s = combineSentence s ! SPreO ! (InS | PreV) ! SOV ;
  useS s = ss (combineSentence s ! (SPreS | SPreV | SPreO | SPreNeg) ! (PreS | PreV | PreO | PreNeg | InV | InS) ! SOV) ;
  --    useS2 s = combineSentence s ! PreV ! SOV ;
  --    locNP np1 np2 = lin NP (mkNP (lin NP np1) (lin Adv { s = np2.preap.s ! Ag np2.g np2.n Gen ++ np2.adv.s ++ np2.s ! Gen ++ np2.postap.s ! Ag np2.g np2.n Gen } ));
  -- useNPCS np = np.preap.s ! Ag np.g np.n Nom ++ np.adv.s ++ np.s ! Nom ++ np.postap.s ! Ag np.g np.n Nom ;
  -- conjCS conj cs1 cs2 = conj.s1 ++ cs1 ++ conj.s2 ++ cs2 ;
};