concrete ABC of ABCAbs = open Prelude in {
  lincat
    A,B,C,D,E,F,G = SS ;
  lin
    a b = b ;
    b = ss "b" ;
    c d e f = cc2 ( cc2 d e ) f ;
    d = ss "d" ;
    e = ss "e" ;
    f = ss "f" ;
    g a c = cc2 a c ;
}