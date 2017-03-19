--# -path=/home/herb/src/own/GF-latin
concrete PrimaEng of Prima =
  CatEng **
  open LexiconEng, ParadigmsEng,GrammarEng,ResEng,Prelude in
  {
  lin
    a_A = { s = \\_ => "*Adjective" };
    pn_PN = { s = \\_ => "*ProperName" ; g = Neutr } ;
    n_N = { s = \\_,_ => "*Noun" ; g = Neutr } ;
    adv_Adv = { s = "*Adverb" } ;
    v_V = { s = \\_ => "*IntransitiveVerb" ; isRefl = False ; p = []} ;
    v2_V2 = { s = \\_ => "*TransitiveVerb" ; isRefl = False ; p = [] ; c2 = [] } ;
    ap_AP = { s = \\_ => "*AdjectivePhrase" ; isPre = True } ;
    vp_VP = { s = \\_,_,_,_,_ => { adv = [] ; aux = [] ; fin = "*VerbPhrase" ; inf = "*VerbPhrase" } ; ad = \\_ => [] ; ext = [] ; inf = [] ; isSimple = True ; p = [] ; prp = [] ; ptp = [] ; s2 = \\_ => []} ;
    np_NP = { s = \\_ => "*NounPhrase" ; a = AgP3Sg Neutr };
    s_S = { s = "*Sentence" };
    externus_A = mkA "foreign" ;
    magnus_A = LexiconEng.big_A ;
    multus_A = mkA "many" ;
    Romanus_A = mkA "Roman" ;
    saepe_Adv = mkAdv "often" ;
    Caesar_N = mkN "Caesar" ;
    civitas_N = mkN "society" ;
    Germanus_N = mkN "Germanic" ;
    hostis_N = mkN "enemy" ;
    imperator_N = mkN "Emperor" ;
    imperium_N = mkN "empire" ;
    provincia_N = mkN "province" ;
    Augustus_PN = mkPN (mkN "Augustus") ;
    Gallia_PN = mkPN (mkN "Gaul") ;
    Africa_PN = mkPN (mkN "Africa") ;
    dicere_V = mkV "say" ;
--    esse_V = predAux auxBe ;
    devenire_V2 = mkV2 (mkV "become") ;
    habere_V2 = have_V2 ;
    tenere_V2 = LexiconEng.hold_V2 ;
    vincere_V2 = mkV2 ( mkV "defeat" ) ;
    he_PP = he_Pron ;
    lesson1APfromA = PositA ;
    lesson1APfromV2 v2 = { s = \\_ => v2.s ! VPPart ; isPre = True } ; -- PastPartAP (SlashV2a v2);
    lesson1ClfromNPVP = PredVP ;
    lesson1NPfromPN = UsePN ;
    lesson1NPfromPron = UsePron ;
    lesson1NPfromCNsg cn = DetCN (DetQuant DefArt NumSg) cn ;
    lesson1NPfromCNpl cn = DetCN (DetQuant DefArt NumPl) cn ;
    lesson1NPfromNPandNP np1 np2 = ConjNP and_Conj (BaseNP np1 np2) ;
    lesson1CNfromN = UseN ;
    lesson1CNfromAPCN a cn = (AdjCN a cn) ;
    lesson1CNfromCNNP = ApposCN ;
    lesson1VPfromV = UseV ;
    lesson1VPfromV2NP v2 np = ComplSlash (SlashV2a v2) np ;
    lesson1VPfromA a = UseComp (CompAP (PositA a)) ;
    lesson1VPfromCN cn = UseComp (CompCN cn) ;
    lesson1SfromCl = UseCl (TTAnt TPres ASimul) PPos ;
    lesson1SfromAdvS = AdvS ;
}