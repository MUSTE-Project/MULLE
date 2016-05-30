abstract Levels = {
  flags
    startcat = Level0;
  cat
    Level0; Level1; Level2;
    Token0; Token1; Token2;
  fun
    l0: Level1 -> Level0;
    l1o0: Level2 -> Level1;
    l1o1: Level1;
    l2 : Token0 -> Token1 -> Token2 -> Level2;
    t0 : Token0;
    t1o0 : Token1;
    t1o1 : Token1;
    t2: Token2;
}