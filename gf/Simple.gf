abstract Simple = {
  cat
    S ; NP ; AP ; VP ; Det ; A ; N ; V ;
  fun
    defSg_Det : Det ;
    defPl_Det : Det ;
    indefSg_Det : Det ;
    indefPl_Det : Det ;
    old_A : A ;
    man_N : N ;
    woman_N : N ;
    eat_V : V ;
    bread_N : N ;
    mkNP1 : Det -> AP -> NP ;
    mkAP : A -> N -> AP ;
    mkNP2 : Det -> N -> NP ;
    mkVP1 : V -> VP ;
    mkVP2 : V -> NP -> VP ;
    mkS : NP -> VP -> S ;
    
  }