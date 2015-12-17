incomplete concrete AnimalC of Animal = {
  param Definit = Def | Indef ;
	Number = Sg | Pl ;
  lincat
    S = { s : Definit => Number => Definit => Number => Str } ;
    Action = { s : Number => Str } ;
    Animal , Object = { s : Definit => Number => Str } ;
  lin
    abuse a = a ;
    apply p s o = { s = \\d,n,d2,n2 => s.s ! d ! n ++ p.s ! n ++ o.s ! d2 ! n2 } ;
}