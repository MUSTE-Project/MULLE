
concrete ImperativeCnc of Imperative = open Prelude in {

flags startcat = Program ;

lincat

  Digit, Number, Bool, Strng = SS ;
  Var, ListVar, Args = SS ;
  Value, ListValue, Values = SS ;
  Stmt, Stmts, Block = SS ;
  Function, ListFun = SS ;
  Name, Progname, Program = SS ;
  Binop, Uniop = Oper ;

lin

  default_a = ss "a" ;
  b = ss "b" ;
  c = ss "c" ;
  d = ss "d" ;
  e = ss "e" ;
  f = ss "f" ;
  i = ss "i" ;
  j = ss "j" ;
  k = ss "k" ;
  x = ss "x" ;
  y = ss "y" ;
  z = ss "z" ;

  default_d0 = ss "0" ;
  d1 = ss "1" ;
  d2 = ss "2" ;
  d3 = ss "3" ;
  d4 = ss "4" ;
  d5 = ss "5" ;
  d6 = ss "6" ;
  d7 = ss "7" ;
  d8 = ss "8" ;
  d9 = ss "9" ;

  digit  d   = d ;
  dignum d n = ss (d.s ++ bind ++ n.s) ;
  number   n = n ;

  true   = ss "true" ;
  false  = ss "false" ;
  bool b = b ;

  default_s1 = ss "s" ;
  s2 = ss "t" ;
  s3 = ss "u" ;
  s4 = ss "abc" ;
  s5 = ss "xyz" ;
  s6 = ss "sst" ;
  s7 = ss "sax" ;
  s8 = ss "yxa" ;
  s9 = ss "apa" ;

  str s = ss ("\"" ++ s.s ++ "\"") ;

  main = ss "main" ;
  run  = ss "run" ;
  default_f1   = ss "f" ;
  f2   = ss "f'" ;
  f3   = ss "g" ;
  f4   = ss "g'" ;

  program name fs = ss ("program" ++ name.s ++ ";" ++ fs.s) ;

  onefunction f = f ;
  addfunction   = cc2 ;
  function name args block = ss ("function" ++ name.s ++ bind ++ paren args.s ++ block.s) ;

  noargs      = ss [] ;
  args    x   = x ;
  onearg  x   = x ;
  consarg x y = ss (x.s ++ bind ++ "," ++ y.s) ;

  nil = ss [] ;
  seq s1 s2 = ss (s1.s ++ s2.s) ;
  block stmts = ss ("{" ++ stmts.s ++ "}") ;

  default_stmt = ss ("null" ++ ";") ;
  print  v = ss ("print" ++ v.s ++ ";") ;
  return v = ss ("return" ++ v.s ++ ";") ;
  ifthen b ifblock = ss ("if" ++ b.s ++ "then" ++ ifblock.s) ;
  ifthenelse b ifblock elseblock = ss ("if" ++ b.s ++ "then" ++ ifblock.s ++ "else" ++ elseblock.s) ; 
  while b whileblock = ss ("while" ++ b.s ++ "do" ++ whileblock.s) ;
  for x from to block = ss ("for" ++ x.s ++ "in" ++ from.s ++ "to" ++ to.s ++ "do" ++ block.s) ; 

  assign op x v = ss (x.s ++ op.assign ++ v.s ++ ";") ;

  default_val  = ss "…" ;
  parens     v = parenss v ;
  use    x     = x ;
  infix op u v = ss (u.s ++ op.value ++ v.s) ;
  prefix op  v = ss (op.value ++ v.s) ;
  call  f args = ss (f.s ++ bind ++ paren args.s) ;

  default_op = mkoper "•" ;
  plus   = mkoper "+" ;
  minus  = mkoper "−" ;
  times  = mkoper "×" ;
  divide = mkoper "÷" ;
  concat = mkoper "++" ;
  and    = mkoper "∧" ;
  or     = mkoper "∨" ;
  equal  = {value = "="; assign = ":="} ;
  noteq  = mkoper "≠" ;
  lt     = mkoper "<" ;
  gt     = mkoper ">" ;
  le     = mkoper "≤" ;
  ge     = mkoper "≥" ;

  negate = mkoper "−" ;
  not    = mkoper "¬" ;

  novalues    = ss [] ;
  values    v = v ;
  onevalue  v = v ;
  consval u v = ss (u.s ++ bind ++ "," ++ v.s) ;

oper

  bind : Str = BIND ;
  -- bind : Str = [] ;

  Oper : Type = {value : Str; assign : Str} ;
  mkoper : Str -> Oper = \op -> {value = op; assign = op + "="} ;

}
