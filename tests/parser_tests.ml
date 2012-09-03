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
  let num_5 = mk_exp (Num 5) 8 in
  let assign_5 = mk_exp (Assign (x, num_5)) 4 in
  let undef = mk_exp Undefined 4 in
  let seq = mk_exp (Seq (var_x, assign_5)) 4 in
  assert_equal (Seq (seq, undef)) exp.stx
  
let test_var_list () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "var x = 5, y = null" in
  let var_x = mk_exp (VarDec "x") 4 in
  let x = mk_exp (Var "x") 4 in
  let num_5 = mk_exp (Num 5) 8 in
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
  let zero = mk_exp (Num 0) 5 in
  assert_equal (mk_exp (CAccess (this, zero)) 0) exp

let suite = "Testing Parser" >:::
  ["test var" >:: test_var;
   "test var with assignment" >:: test_var_value;
   "test var list" >:: test_var_list;
   "test regexp" >:: test_regexp;
   "test regexp with flags" >:: test_regexp_with_flags;
   "test not" >:: test_not;
   "test_caccess" >:: test_caccess
  ]