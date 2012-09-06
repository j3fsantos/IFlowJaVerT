open OUnit
open Syntax
open Symb_execution
    
let test_var () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "var x" in
  assert_equal (mk_exp (VarDec "x") 4) exp
  
let test_var_value () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "var x = 5" in
  let var_x = mk_exp (VarDec "x") 4 in
  let x = mk_exp (Var "x") 4 in
  let num_5 = mk_exp (Num 5.0) 8 in
  let assign_5 = mk_exp (Assign (x, num_5)) 4 in
  let undef = mk_exp Undefined 4 in
  let seq = mk_exp (Seq (var_x, assign_5)) 4 in
  assert_equal (Seq (seq, undef)) exp.stx
  
let test_var_list () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "var x = 5, y = null" in
  let var_x = mk_exp (VarDec "x") 4 in
  let x = mk_exp (Var "x") 4 in
  let num_5 = mk_exp (Num 5.0) 8 in
  let assign_5 = mk_exp (Assign (x, num_5)) 4 in
  let undef = mk_exp Undefined 4 in
  let var_x_5 = mk_exp (Seq (var_x, assign_5)) 4 in
  let seq1 = mk_exp (Seq (var_x_5, undef)) 4 in
  let var_y = mk_exp (VarDec "y") 11 in
  let y = mk_exp (Var "y") 11 in
  let nul = mk_exp Null 15 in
  let assign_nul = mk_exp (Assign (y, nul)) 11 in
  let undef2 = mk_exp Undefined 11 in
  let var_y_nul = mk_exp (Seq (var_y, assign_nul)) 11 in
  let seq2 = mk_exp (Seq (var_y_nul, undef2)) 11 in
  assert_equal (Seq (seq1, seq2)) exp.stx
  
let test_regexp () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "/^\\s+/" in
  assert_equal (mk_exp (RegExp ("^\\s+", "")) 0) exp
  
let test_regexp_with_flags () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "/^\\s+/g" in
  assert_equal (mk_exp (RegExp ("^\\s+", "g")) 0) exp
  
let test_not () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "!selector" in
  let selector = mk_exp (Var "selector") 1 in
  assert_equal (mk_exp (Unary_op (Not, selector)) 0) exp
  
let test_caccess () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "this[0]" in
  let this = mk_exp This 0 in
  let zero = mk_exp (Num 0.0) 5 in
  assert_equal (mk_exp (CAccess (this, zero)) 0) exp
  
let test_and () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a && b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 5 in
  assert_equal (mk_exp (BinOp (a, And, b)) 0) exp
  
let test_array_literal () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "[,x,,y,]" in
  let e1 = mk_exp Undefined 1 in
  let x = mk_exp (Var "x") 2 in
  let e2 = mk_exp Undefined 4 in  
  let y = mk_exp (Var "y") 5 in
  let length = mk_exp (Num 4.0) 0 in
  assert_equal (mk_exp (Obj [("0", e1);("1", x);("2", e2);("3", y);("length", length)]) 0) exp
  
let test_ge () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "1 >= 2" in
  let one = mk_exp (Num 1.0) 0 in
  let two = mk_exp (Num 2.0) 5 in
  assert_equal (mk_exp (BinOp (one, Ge, two)) 0) exp
  
let test_or () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a || b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 5 in
  assert_equal (mk_exp (BinOp (a, Or, b)) 0) exp
  
let test_not_triple_eq () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a !== b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 6 in
  assert_equal (mk_exp (BinOp (a, NotTripleEqual, b)) 0) exp
  
let test_hook () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a >= b ? a : b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 5 in
  let ab = mk_exp (BinOp (a, Ge, b)) 0 in
  let a9 = mk_exp (Var "a") 9 in
  let b13 = mk_exp (Var "b") 13 in
  assert_equal (mk_exp (If (ab, a9, b13)) 0) exp
  
let test_instanceof () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a instanceof b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 13 in
  assert_equal (mk_exp (BinOp (a, InstanceOf, b)) 0) exp
  
let test_typeof () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "typeof selector" in
  let selector = mk_exp (Var "selector") 7 in
  assert_equal (mk_exp (Unary_op (TypeOf, selector)) 0) exp
  
let test_pos () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "+(a + 1)" in
  let a = mk_exp (Var "a") 2 in
  let one = mk_exp (Num 1.0) 6 in
  let a1 = mk_exp (BinOp (a, Plus, one)) 2 in
  assert_equal (mk_exp (Unary_op (Positive, a1)) 0) exp
  
let test_dec_pre () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "--a" in
  let a = mk_exp (Var "a") 2 in
  assert_equal (mk_exp (Unary_op (Pre_Decr, a)) 0) exp
  
let test_dec_post () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a--" in
  let a = mk_exp (Var "a") 0 in
  assert_equal (mk_exp (Unary_op (Post_Decr, a)) 0) exp
  
let test_inc_pre () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "++a" in
  let a = mk_exp (Var "a") 2 in
  assert_equal (mk_exp (Unary_op (Pre_Incr, a)) 0) exp
  
let test_inc_post () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a++" in
  let a = mk_exp (Var "a") 0 in
  assert_equal (mk_exp (Unary_op (Post_Incr, a)) 0) exp
  
let test_for () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "for (; a < 5; a++ ) { /** @invariant #cScope = [#lg] */ x = 1 }" in
  let empty = mk_exp Skip 5 in
  let a = mk_exp (Var "a") 7 in
  let five = mk_exp (Num 5.0) 11 in
  let condition = mk_exp (BinOp (a, Lt, five)) 7 in
  let a = mk_exp (Var "a") 14 in
  let inc = mk_exp (Unary_op (Post_Incr, a)) 14 in
  let one = mk_exp (Num 1.0) 60 in
  let x = mk_exp (Var "x") 56 in
  let assignment = mk_exp (Assign (x, one)) 56 in
  let body = mk_exp (Seq (assignment, inc)) 0 in
  let loop = mk_exp_with_annot (While (condition, body)) 0 [{atype = Invariant; aformula = "#cScope = [#lg]"}] in
  assert_equal (mk_exp (Seq (empty, loop)) 0) exp

let suite = "Testing Parser" >:::
  ["test var" >:: test_var;
   "test var with assignment" >:: test_var_value;
   "test var list" >:: test_var_list;
   "test regexp" >:: test_regexp;
   "test regexp with flags" >:: test_regexp_with_flags;
   "test not" >:: test_not;
   "test_caccess" >:: test_caccess;
   "test_and" >:: test_and;
   "test_array_literal" >:: test_array_literal;
   "test_ge" >:: test_ge;
   "test_or" >:: test_or;
   "test_not_triple_eq" >:: test_not_triple_eq;
   "test_hook" >:: test_hook;
   "test_instanceof" >:: test_instanceof;
   "test_typeof" >:: test_typeof;
   "test_pos" >:: test_pos;
   "test_dec_pre" >:: test_dec_pre;
   "test_dec_post" >:: test_dec_post;
   "test_inc_pre" >:: test_inc_pre;
   "test_inc_post" >:: test_inc_post;
   "test_for" >:: test_for;
  ]