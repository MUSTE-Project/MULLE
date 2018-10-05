concrete ExemplumLexSpa of ExemplumLex = CatSpa ** ExemplumLexI
  with (Cat=CatSpa), (Grammar=GrammarSpa), (Lexicon=LexiconSpa) **
  open ParadigmsSpa, (Irreg=IrregSpa), (Diff=DiffSpa), Prelude in {

lin
  copula_V = mkV2 Diff.copula ;
  
}
