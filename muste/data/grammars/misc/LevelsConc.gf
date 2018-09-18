concrete LevelsConc of Levels = open Prelude in {
  param Rev = T | F ;
  lincat
    Token0, Token1, Token2 = SS;
    Level0, Level1, Level2 = Rev => SS ;
  lin
    l0 l1 = \\rev => ss3 "(L0 " (l1 ! rev).s ")";
    l1o0 l2 = \\rev => ss3 "(L1 " (l2 ! rev).s ")";
    l1o1 = \\rev => ss "L1";
    l2 t0 t1 t2 = table Rev { F => cc3 (ss "(L2 ")  (cc3 t0 t1 t2) (ss ")") ;
			      T => cc3 (ss "(L2 ")  (cc3 t2 t1 t0) (ss ")")
      };
    t0 = ss "T0";
    t1o0 = ss "T1O0";
    t1o1 = ss "T1O1";
    t2 = ss "T2";
    
}