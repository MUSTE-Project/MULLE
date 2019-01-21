--# -path=prelude:abstract:common
abstract ExemplumRules = Cat, Tense ** {

cat
  Utterance ;

fun
  useN     : N    -> CN              ;
  attribCN : AP   -> CN  -> CN       ;
  apposCN  : CN   -> PN  -> CN       ;

  usePN    : PN   -> NP              ;
  usePron  : Pron -> NP              ;
  detCN    : Det  -> CN  -> NP       ;
  advNP    : NP   -> Adv -> NP       ;
  conjNP   : Conj -> NP  -> NP -> NP ;

  useA     : A    -> AP              ;

  prepNP   : Prep -> NP  -> Adv      ;

  intransV : V2   -> VP              ;
  transV   : V2   -> NP  -> VP       ;
  complVA  : V2   -> AP  -> VP       ;
  advVP    : VP   -> Adv -> VP       ;

  simpleCl : NP   -> VP  -> Cl       ;

  useCl    : Pol  -> Ant -> Cl -> S  ;
  useS     : S           -> Utterance;
  focusAdv : Adv  -> S   -> Utterance;
}
