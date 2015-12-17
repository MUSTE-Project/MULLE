concrete AnimalSwe of Animal = AnimalC ** open Prelude in {
  param Gen = Utr | Neutr ; 
  flags coding = utf8 ;
  lin
    drink = verbForm "dricker" ;
    eat = verbForm "äter" ;
    grass = nounForm "gräs" "gräset" "gräs" "gräsen" ;
    lamb = nounForm "lamm" "lammet" "lamm" "lammen" ;
    milk = nounForm "mjölk" "mjölken" nonExist nonExist ;
    produce = verbForm "tillverkar" ;
    sheep = nounForm "får" "fåret" "får" "fåren" ;
    wolf = nounForm "varg" "vargen" "vargar" "vargarna" ;
    wool = nounForm "ull" "ullen" nonExist nonExist ;
  oper
    verbForm : Str -> { s : Number => Str } =
      \f -> { s = \\_ => f } ;
    nounForm : Str -> Str -> Str -> Str -> { s : Definit => Number => Str } =
      \f1,f2,f3,f4 ->
      { s = \\d,n =>
	  table {
	    <Def,Sg> => f1 ;
	    <Def,Pl> => f2 ;
	    <Indef,Sg> => f3 ;
	    <Indef,Pl> => f4
	  } ! <d,n>
      };
  }