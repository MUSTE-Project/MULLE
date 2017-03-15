--# -path=/home/herb/src/own/GF-latin
abstract PrimaAbs = Cat ** {
  flags
    startcat = S;
  fun
    externus_A : A ;
    magnus_A : A ;
    multus_A : A ;
    Romanus_A : A ;
    saepe_Adv : Adv ;
    Caesar_N : N ;
    civitas_N : N ;
    Germanus_N : N ;
    hostis_N : N ;
    imperator_N : N ;
    imperium_N : N ;
    provincia_N : N ;
    Augustus_PN : PN ;
    Gallia_PN : PN ;
    Africa_PN : PN ;
    dicere_V : V ;
    esse_V : V ;
    devenire_V2 : V2 ;
    habere_V2 : V2 ;
    tenere_V2 : V2 ;
    vincere_V2 : V2 ;
    he_PP : Pron ;
    lesson1APfromA : A -> AP ;
    lesson1APfromV2 : V2 -> AP ;
    lesson1ClfromNPVP : NP -> VP -> Cl ;
    lesson1NPfromPN : PN -> NP ;
    lesson1NPfromPron : Pron -> NP ;
    lesson1NPfromCNsg : CN -> NP ;
    lesson1NPfromCNpl : CN -> NP ;
    lesson1NPfromNPandNP : NP -> NP -> NP ;
    lesson1CNfromN : N -> CN ;
    lesson1CNfromAPCN : AP -> CN -> CN ;
    lesson1CNfromCNNP : CN -> NP -> CN ;
    lesson1SfromCl : Cl -> S ;
    lesson1SfromAdvS : Adv -> S -> S ;
    lesson1VPfromV : V -> VP ;
    lesson1VPfromV2NP : V2 -> NP -> VP ;
    lesson1VPfromA : A -> VP ;
    lesson1VPfromCN : CN -> VP ;
}