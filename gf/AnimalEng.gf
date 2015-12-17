concrete AnimalEng of Animal = AnimalC ** open Prelude in {
  lin
    drink = verbForm "drink";
    eat = verbForm "eat";
    lamb = nounForm "lamb" ;
    grass = massNoun "grass" ;
    milk = massNoun "milk" ;
    sheep = nounForms "sheep" "sheep" ;
    wolf = nounForms "wolf" "wolves" ;
    wool = massNoun "wool" ; 
    produce = verbForm "produce" ;
  oper
    verbForm : Str -> { s : Number => Str } =
      \f -> { s = table { Sg => f + "s" ; Pl => f } } ;
    nounForm : Str -> { s : Definit => Number => Str } =
      \f -> nounForms f ( f + "s" ) ;
    nounForms : Str -> Str -> { s : Definit => Number => Str } =
      \s,p -> { s = \\d,n =>
		table { <_,Def> => "the" ; <Sg,Indef> => "a" ; _ => "" } ! <n,d> ++
		table { Sg => s ; Pl => p } ! n} ;
    massNoun : Str -> { s : Definit => Number => Str } =
      \f -> { s = \\d,_ => case d of { Def => "the" ++ f ; Indef => f } };
  }