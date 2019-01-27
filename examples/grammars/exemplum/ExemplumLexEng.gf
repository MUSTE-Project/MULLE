concrete ExemplumLexEng of ExemplumLex = CatEng ** ExemplumLexI
  with (Cat=CatEng), (Grammar=GrammarEng), (Lexicon=LexiconEng) **
  open ParadigmsEng, Prelude in {

lin
  -- Note: The English RGL cannot encode the Copula as a regular verb, this is the best we can do:
  copula_V = mkV2 (mkV ("be"|"are") "is" "was" "been" "being") ;

}
