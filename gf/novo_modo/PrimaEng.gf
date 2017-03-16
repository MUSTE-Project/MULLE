--# -path=/home/herb/src/own/GF-latin
concrete PrimaEng of Prima =
  CatEng **
  open LexiconEng, ParadigmsEng,GrammarEng in
  {
  lin
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
    vincere_V2 = LexiconEng.win_V2 ;
    he_PP = he_Pron ;
    lesson1APfromA = PositA ;
--    lesson1APfromV2 v2 = PastPartAP (SlashV2a v2);
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