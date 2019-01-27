
abstract Imperative = {

flags startcat = Program ;

cat

  Digit ; Number ; Bool ; Strng ;
  Var ; ListVar ; Args ;
  Value ; ListValue ; Values ;
  Stmt ; Stmts ; Block ;
  Function ; ListFun ;
  Name ; Progname ; Program ;
  Binop ; Uniop ;

fun

  default_a, b, c, d, e, f, i, j, k, x, y, z : Var ;

  default_d0, d1, d2, d3, d4, d5, d6, d7, d8, d9 : Digit ;
  digit : Digit -> Number ;
  dignum : Digit -> Number -> Number ;
  number : Number -> Value ;

  true, false : Bool ;
  bool : Bool -> Value ;

  default_s1, s2, s3, s4, s5, s6, s7, s8, s9 : Strng ;
  str : Strng -> Value ;

  main, run, default_f1, f2, f3, f4 : Name ;
  program : Name -> ListFun -> Program ;
  onefunction : Function -> ListFun ;
  addfunction : ListFun -> Function -> ListFun ;
  function : Name -> Args -> Block -> Function ;

  noargs : Args ;
  args : ListVar -> Args ;
  onearg : Var -> ListVar ; 
  consarg : Var -> ListVar -> ListVar ;

  nil : Stmts ;
  seq : Stmt -> Stmts -> Stmts ;
  block : Stmts -> Block ;

  default_stmt : Stmt ;
  print : Value -> Stmt ;
  return : Value -> Stmt ;
  ifthen : Value -> Block -> Stmt ;
  ifthenelse : Value -> Block -> Block -> Stmt ;
  while : Value -> Block -> Stmt ;
  for : Var -> Value -> Value -> Block -> Stmt ;
  assign : Binop -> Var -> Value -> Stmt ;

  default_val : Value ;
  parens : Value -> Value ;
  use : Var -> Value ;
  infix : Binop -> Value -> Value -> Value ;
  prefix : Uniop -> Value -> Value ;
  call : Name -> Values -> Value ;

  default_op : Binop ;
  plus, minus, times, divide : Binop ;
  concat : Binop ;
  and, or : Binop ;
  equal, noteq, lt, gt, le, ge : Binop ;

  negate, not : Uniop ;

  novalues : Values ;
  values : ListValue -> Values ;
  onevalue : Value -> ListValue ;
  consval : Value -> ListValue -> ListValue ;

}
