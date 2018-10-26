
concrete ImperativeCnc of Imperative = open Prelude in {

flags startcat = Program ;

lincat

  Digit, Number, Bool, Strng = SS ;
  Var, ListVar, Args = SS ;
  Value, ListValue, Values = SS ;
  Stmt, Stmts, Block = IndentSS ;
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

  str s = ss ("\"" ++ bind ++ s.s ++ bind ++ "\"") ;

  main = ss "main" ;
  run  = ss "run" ;
  default_f1   = ss "f" ;
  f2   = ss "f'" ;
  f3   = ss "g" ;
  f4   = ss "g'" ;

  program name fs = ss (
    "program" ++ name.s ++ nl ++ fs.s) ;

  onefunction f = f ;
  addfunction   = cc2 ;
  function name args block = ss (
    "function" ++ name.s ++ bind ++ args.s ++ block.s ! I1 ++ nl) ;

  noargs      = ss (paren bind) ;
  args    x   = parenss x ;
  onearg  x   = x ;
  consarg x y = ss (x.s ++ bind ++ "," ++ y.s) ;

  nil = {s = \\_ => []} ;
  seq s1 s2 =
    {s = \\ind => indent ind ++ s1.s ! ind ++ bind ++ ";" ++ nl ++ s2.s ! ind} ;
  block stmts =
    {s = \\ind => "{" ++ nl ++ stmts.s ! nextindent ind ++ indent ind ++ "}"} ;

  default_stmt = {s = \\_ => "null"} ;
  print  v = {s = \\_ => "print" ++ v.s} ;
  return v = {s = \\_ => "return" ++ v.s} ;
  ifthen b ifblock =
    {s = \\ind => "if" ++ b.s ++ "then" ++ ifblock.s ! ind} ;
  ifthenelse b ifblock elseblock = 
    {s = \\ind => "if" ++ b.s ++ "then" ++ ifblock.s ! ind ++
       "else" ++ elseblock.s ! ind} ; 
  while b whileblock = 
    {s = \\ind => "while" ++ b.s ++ "do" ++ whileblock.s ! ind} ;
  for x from to block = 
    {s = \\ind => "for" ++ x.s ++ "in" ++ from.s ++ "to" ++ to.s ++
       "do" ++ block.s ! ind} ; 

  assign op x v = {s = \\_ => x.s ++ op.assign ++ v.s} ;

  default_val  = ss "…" ;
  parens     v = parenss v ;
  use    x     = x ;
  infix op u v = ss (u.s ++ op.value ++ v.s) ;
  prefix op  v = ss (op.value ++ v.s) ;
  call  f args = ss (f.s ++ bind ++ args.s) ;

  default_op = mkoper "•" ;
  plus   = mkoper "+" ;
  minus  = mkoper "−" ;
  times  = mkoper "×" ;
  divide = mkoper "÷" ;
  concat = mkoper "++" ;
  and    = mkoper "∧" ;
  or     = mkoper "∨" ;
  equal  = mkoper "=" ;
  noteq  = mkoper "≠" ;
  lt     = mkoper "<" ;
  gt     = mkoper ">" ;
  le     = mkoper "≤" ;
  ge     = mkoper "≥" ;

  negate = mkoper "−" ;
  not    = mkoper "¬" ;

  novalues    = ss (paren bind) ;
  values    v = parenss v ;
  onevalue  v = v ;
  consval u v = ss (u.s ++ bind ++ "," ++ v.s) ;

oper

  bind : Str = BIND ;
  indentspace : Str = "&_" ;
  nl : Str = "&/" ; 

  -- bind : Str = [] ;
  -- indentspace : Str = "  " ;
  -- nl : Str = "\n" ;

  Oper : Type = {value : Str; assign : Str} ;
  mkoper : Str -> Oper = \op -> {value = op; assign = op + "="} ;

  IndentSS : Type = {s : Indent => Str} ;

  indent : Indent -> Str = \ind -> case ind of {
    I1 => [] ;
    I2 => indentspace ;
    I3 => indentspace ++ indentspace ;
    I4 => indentspace ++ indentspace ++ indentspace ;
    I5 => indentspace ++ indentspace ++ indentspace ++ indentspace 
    } ;

  nextindent : Indent -> Indent = \ind -> case ind of {
    I1 => I2 ; I2 => I3 ; I3 => I4 ; _ => I5
    } ;

param

  Indent = I1 | I2 | I3 | I4 | I5 ;

}
