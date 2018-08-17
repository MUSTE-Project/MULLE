incomplete concrete PrimaRulesI of PrimaRules = Cat, Conjunction **
  open Syntax in {

lincat
  ListNP = Conjunction.ListNP;

lin
    
  useA a = lin AP (mkAP (lin A a)) ;
  simpleCl np vp = lin Cl (mkCl (lin NP np) (lin VP vp)) ;
  usePN pn = lin NP (mkNP (lin PN pn)) ;
  usePron pron = lin NP (mkNP (lin Pron pron)) ;
  useCNdefsg cn = lin NP (mkNP theSg_Det (lin CN cn)) ;
  useCNindefsg cn = lin NP (mkNP aSg_Det (lin CN cn)) ;
  useCNindefpl cn = lin NP (mkNP aPl_Det (lin CN cn));
  complexNP det cn = lin NP (mkNP (lin Det det) (lin CN cn)) ;
  conjNP np1 np2 = lin ListNP (mkListNP (lin NP np1) (lin NP np2)) ;
  extConjNP lnp np = lin ListNP (mkListNP (lin NP np) (lin ListNP lnp) );
  useConjNP conj lnp = lin NP (mkNP (lin Conj conj) (lin ListNP lnp));
  useN n = lin CN (mkCN (lin N n)) ;
  attribCN ap cn = lin CN (mkCN (lin AP ap) (lin CN cn)) ;
  apposCNdefsg cn pn = lin NP (mkNP theSg_Det (mkCN cn (mkNP pn)));
  useCl cl = lin S (mkS (mkTemp presentTense simultaneousAnt) positivePol (lin CL cl)) ;
  advS adv s = lin S (mkS (lin Adv adv) (lin S s)) ;
  intransV v = lin VP (mkVP (lin V v)) ;
  transV v2 np = lin VP (mkVP (lin V2 v2) (lin NP np)) ;
  complVA va ap = lin VP (mkVP va ap) ;
  --    useS s = lin Utt (mkUtt (lin S s)) ;

}