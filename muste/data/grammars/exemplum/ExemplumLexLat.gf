--# -path=prelude:abstract:common:latin
concrete ExemplumLexLat of ExemplumLex = CatLat ** ExemplumLexI
  with (Cat=CatLat), (Grammar=GrammarLat), (Lexicon=LexiconLat) **
  open ParadigmsLat, (Irreg=IrregLat), Prelude in {

lin
  copula_V = mkV2 Irreg.be_V ;

}
