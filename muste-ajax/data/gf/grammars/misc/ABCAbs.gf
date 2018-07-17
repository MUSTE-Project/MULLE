abstract ABCAbs = {
  flags
    startcat = S ;
  cat
    S; A; B; C;
  fun
    s : A -> S;
    a : A ;
    b : B ;
    c : C ;
    f : A -> B -> A ;
    g : B -> C -> B ;
    h : A -> A -> A -> A ;
}