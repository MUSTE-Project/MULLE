incomplete concrete QuartaLexI of QuartaLex = Cat ** open Structural,Lexicon,SecundaLex,TertiaLex,Syntax in {
  lin
    liber_N = Lexicon.book_N ;
    scribere_V2 = Lexicon.write_V2 ;
    legere_V2 = Lexicon.read_V2 ;
    et_Conj = SecundaLex.et_Conj ; -- Secunda
    nos_Pron = Structural.we_Pron ;
    in_Prep = TertiaLex.in_Prep ; -- Tertia
    tres_Num = mkNum (mkNumeral n3_Unit) ;
    alius_A = SecundaLex.alius_A ; -- Pron?
    lingua_N = TertiaLex.lingua_N ; -- Tertia
    aliquis_Pron = SecundaLex.aliquis_Pron ; -- Secunca
    -- noster_Pron : Pron ; -- included in we_Pron
    quod_Conj = TertiaLex.quod_Conj ;
    tertius_Ord = mkOrd (mkNumeral n3_Unit) ;
}