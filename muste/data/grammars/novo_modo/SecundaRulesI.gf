incomplete concrete SecundaRulesI of SecundaRules = Cat **
  open Syntax, PrimaRules in {

lincat
  ListNP = PrimaRules.ListNP ;

lin
  -- Prima
  useA = PrimaRules.useA ;
  simpleCl = PrimaRules.simpleCl ;
  usePN = PrimaRules.usePN ;
  usePron = PrimaRules.usePron ;
  useCNdefsg = PrimaRules.useCNdefsg ;
  useCNindefpl = PrimaRules.useCNindefpl ;
  --    conjNP conj np1 np2 = lin NP (mkNP (lin Conj conj) (lin NP np1) (lin NP np2)) ;
  conjNP = PrimaRules.conjNP ;
  extConjNP = PrimaRules.extConjNP ;
  useConjNP = PrimaRules.useConjNP ; 
  useN = PrimaRules.useN ;
  attribCN = PrimaRules.attribCN ;
  advS = PrimaRules.advS ;
  intransV = PrimaRules.intransV ;
  transV = PrimaRules.transV ;
  complVA = PrimaRules.complVA ;
  presS = PrimaRules.useCl;
  
  pastS cl = lin S (mkS (mkTemp pastTense simultaneousAnt) positivePol (lin Cl cl) ) ;
  negPastS cl = lin S (mkS (mkTemp pastTense simultaneousAnt) negativePol (lin Cl cl) ) ;

  -- Secunda
  useCNdefpl cn = lin NP (mkNP thePl_Det (lin CN cn));
  prepNP np1 prep np2 =
    let pp = lin Adv (mkAdv (lin Prep prep) (lin NP np2) ) in
    lin NP (mkNP np1 pp) ;

  useVVCl np vv vp = lin Cl (mkCl (lin NP np) (lin VV vv) (lin VP vp));

  advNP a np = lin NP (mkNP np a) ;
  
  --     attribNP np1 np2 = lin Cl (mkCl (lin NP np1) (lin NP np2)) ;



  --     --    useCNpl cn = lin NP (mkNP aPl_Det (lin CN cn));


  --     useNdefpl n = lin NP (mkNP thePl_Det (lin N n) ) ;
  --     useNindefpl n = lin NP (mkNP aPl_Det (lin N n) );

  possNP np1 np2 = lin NP (mkNP (lin NP np1) (lin Adv (mkAdv possess_Prep (lin NP np2)))) ;


  -- --    presS cl = lin S (mkS (mkTemp presentTense simultaneousAnt) positivePol (lin Cl cl) ) ;


  -- --    conjS conj s1 s2 = lin S (mkS (lin Conj conj) (lin S s1) (lin S s2)) ;
  --     advVP adv vp = lin VP (mkVP (lin Adv adv) (lin VP vp) ) ;
  --     advVP2 adv vp = lin VP (mkVP (lin VP vp) (lin Adv adv) ) ;
  -- --    apposCN cn np = lin CN (mkCN (lin CN cn) (lin NP np)) ;
  --     advCN adv cn = lin CN (mkCN (lin CN cn) (lin Adv adv )) ;

  --     --    complN n = lin VP (mkVP (lin N n)) ;
  --     complCN cn = lin VP (mkVP (lin CN cn)) ;

}

-- Abstract	UttS (UseCl (TTAnt TPres ASimul) PPos (PredVP (DetNP (DetQuant DefArt NumPl)) (ComplVV want_VV (ComplSlash (SlashV2a kill_V2) (DetCN (DetQuant DefArt NumPl) (UseN man_N))))))
-- API   		mkUtt ( mkS ( mkCl ( mkNP ( mkDet the_Quant pluralNum ) ) want_VV ( mkVP kill_V2 ( mkNP the_Quant pluralNum man_N ) ) ) )