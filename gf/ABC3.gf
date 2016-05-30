concrete ABC3 of ABCAbs = open Prelude in {
  lincat
    A,B,C = { a : Str ; b : Str } ;
    S = SS ;
  lin
    s a = ss (a.a ++ a.b) ;
    a = { a = "<a" ; b = "a>" };
    b = { a = "<b" ; b = "b>" } ;
    c = { a = "<c" ; b = "c>" } ;
    f a b = { a = a.a ++ b.a ; b = a.b ++ b.b } ;
    g b c ={ a = "" ; b = b.a ++ b.b } ;
}