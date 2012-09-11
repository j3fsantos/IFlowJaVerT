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
  assert_equal (mk_exp (BinOp (a, Boolean And, b)) 0) exp
  
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
  assert_equal (mk_exp (BinOp (one, Comparison Ge, two)) 0) exp
  
let test_or () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a || b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 5 in
  assert_equal (mk_exp (BinOp (a, Boolean Or, b)) 0) exp
  
let test_not_triple_eq () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a !== b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 6 in
  assert_equal (mk_exp (BinOp (a, Comparison NotTripleEqual, b)) 0) exp
  
let test_hook () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a >= b ? a : b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 5 in
  let ab = mk_exp (BinOp (a, Comparison Ge, b)) 0 in
  let a9 = mk_exp (Var "a") 9 in
  let b13 = mk_exp (Var "b") 13 in
  assert_equal (mk_exp (If (ab, a9, b13)) 0) exp
  
let test_instanceof () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a instanceof b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 13 in
  assert_equal (mk_exp (BinOp (a, Comparison InstanceOf, b)) 0) exp
  
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
  let a1 = mk_exp (BinOp (a, Arith Plus, one)) 2 in
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
  let condition = mk_exp (BinOp (a, Comparison Lt, five)) 7 in
  let a = mk_exp (Var "a") 14 in
  let inc = mk_exp (Unary_op (Post_Incr, a)) 14 in
  let one = mk_exp (Num 1.0) 60 in
  let x = mk_exp (Var "x") 56 in
  let assignment = mk_exp (Assign (x, one)) 56 in
  let body = mk_exp (Seq (assignment, inc)) 0 in
  let loop = mk_exp_with_annot (While (condition, body)) 0 [{atype = Invariant; aformula = "#cScope = [#lg]"}] in
  assert_equal (mk_exp (Seq (empty, loop)) 0) exp
  
let test_forin () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "for (var prop in oldObj) { obj[prop] = oldObj[prop] }" in
  let varprop = mk_exp (VarDec "prop") 9 in
  let oldObj1= mk_exp (Var "oldObj") 17 in
  let obj = mk_exp (Var "obj") 27 in
  let prop1 = mk_exp (Var "prop") 31 in
  let ca1 = mk_exp (CAccess (obj, prop1)) 27 in
  let oldObj2 = mk_exp (Var "oldObj") 39 in
  let prop2 = mk_exp (Var "prop") 46 in
  let ca2 = mk_exp (CAccess (oldObj2, prop2)) 39 in
  let assignment = mk_exp (Assign (ca1, ca2)) 27 in
  assert_equal (mk_exp (ForIn (varprop, oldObj1, assignment)) 0) exp
  
let test_assign_add () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a += b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 5 in
  assert_equal (mk_exp (AssignOp (a, Plus, b)) 0) exp
  
let test_assign_sub () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a -= b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 5 in
  assert_equal (mk_exp (AssignOp (a, Minus, b)) 0) exp
  
let test_assign_mul () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a *= b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 5 in
  assert_equal (mk_exp (AssignOp (a, Times, b)) 0) exp
  
let test_assign_div () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a /= b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 5 in
  assert_equal (mk_exp (AssignOp (a, Div, b)) 0) exp
  
let test_assign_mod () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a %= b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 5 in
  assert_equal (mk_exp (AssignOp (a, Mod, b)) 0) exp
  
let test_assign_ursh () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a >>>= b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 7 in
  assert_equal (mk_exp (AssignOp (a, Ursh, b)) 0) exp
  
let test_assign_lsh () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a <<= b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 6 in
  assert_equal (mk_exp (AssignOp (a, Lsh, b)) 0) exp
  
let test_assign_rsh () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a >>= b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 6 in
  assert_equal (mk_exp (AssignOp (a, Rsh, b)) 0) exp
  
let test_assign_bitand () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a &= b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 5 in
  assert_equal (mk_exp (AssignOp (a, Bitand, b)) 0) exp
  
let test_assign_bitor () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a |= b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 5 in
  assert_equal (mk_exp (AssignOp (a, Bitor, b)) 0) exp
  
let test_assign_bitxor () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a ^= b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 5 in
  assert_equal (mk_exp (AssignOp (a, Bitxor, b)) 0) exp
  
let test_notequal () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a != b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 5 in
  assert_equal (mk_exp (BinOp (a, Comparison NotEqual, b)) 0) exp
  
let test_gt () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a > b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 4 in
  assert_equal (mk_exp (BinOp (a, Comparison Gt, b)) 0) exp
  
let test_in () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a in b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 5 in
  assert_equal (mk_exp (BinOp (a, Comparison In, b)) 0) exp
  
let test_comma1 () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a , b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 4 in
  assert_equal (mk_exp (Comma (a, b)) 0) exp
  
let test_comma2 () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a, b, c" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 3 in
  let c = mk_exp (Var "c") 6 in
  let ab = mk_exp (Comma (a, b)) 0 in
  assert_equal (mk_exp (Comma (ab, c)) 0) exp
  
let test_negative () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "-a" in
  let a = mk_exp (Var "a") 1 in
  assert_equal (mk_exp (Unary_op (Negative, a)) 0) exp
  
let test_bitnot () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "~a" in
  let a = mk_exp (Var "a") 1 in
  assert_equal (mk_exp (Unary_op (Bitnot, a)) 0) exp
  
let test_void () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "void a" in
  let a = mk_exp (Var "a") 5 in
  assert_equal (mk_exp (Unary_op (Void, a)) 0) exp
  
let test_mod () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a % b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 4 in
  assert_equal (mk_exp (BinOp (a, Arith Mod, b)) 0) exp
  
let test_ursh () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a >>> b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 6 in
  assert_equal (mk_exp (BinOp (a, Arith Ursh, b)) 0) exp
  
let test_lsh () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a << b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 5 in
  assert_equal (mk_exp (BinOp (a, Arith Lsh, b)) 0) exp
  
let test_rsh () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a >> b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 5 in
  assert_equal (mk_exp (BinOp (a, Arith Rsh, b)) 0) exp
  
let test_bitand () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a & b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 4 in
  assert_equal (mk_exp (BinOp (a, Arith Bitand, b)) 0) exp
  
let test_bitor () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a | b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 4 in
  assert_equal (mk_exp (BinOp (a, Arith Bitor, b)) 0) exp
  
let test_bitxor () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "a ^ b" in
  let a = mk_exp (Var "a") 0 in
  let b = mk_exp (Var "b") 4 in
  assert_equal (mk_exp (BinOp (a, Arith Bitxor, b)) 0) exp
  
let test_return () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "function f() {return}" in
  let r = mk_exp (Return None) 14 in
  assert_equal (mk_exp (NamedFun ("f", [], r)) 0) exp
  
let test_return_exp () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "function f() {return g()}" in
  let g = mk_exp (Var "g") 21 in
  let gcall = mk_exp (Call (g, [])) 22 in
  let r = mk_exp (Return (Some gcall)) 14 in
  assert_equal (mk_exp (NamedFun ("f", [], r)) 0) exp
  
let test_do_while () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "do { /** @invariant #cScope = [#lg] */ a = 1 } while (a < 5)" in
  let a = mk_exp (Var "a") 54 in
  let five = mk_exp (Num 5.0) 58 in
  let condition = mk_exp (BinOp (a, Comparison Lt, five)) 54 in
  let a = mk_exp (Var "a") 39 in
  let one = mk_exp (Num 1.0) 43 in
  let assignment = mk_exp (Assign (a, one)) 39 in
  let loop = mk_exp_with_annot (While (condition, assignment)) 0 [{atype = Invariant; aformula = "#cScope = [#lg]"}] in
  assert_equal (mk_exp (Seq (assignment, loop)) 0) exp
  
let test_delete () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "delete a" in
  let a = mk_exp (Var "a") 7 in
  assert_equal (mk_exp (Delete a) 0) exp
  
let test_continue () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "while (a > 5) {/** @invariant #cScope = [#lg] */ a++; continue}" in
  let a = mk_exp (Var "a") 7 in
  let five = mk_exp (Num 5.0) 11 in
  let condition = mk_exp (BinOp (a, Comparison Gt, five)) 7 in
  let a = mk_exp (Var "a") 49 in
  let app = mk_exp (Unary_op (Post_Incr, a)) 49 in
  let cont = mk_exp (Continue None) 54 in
  let body = mk_exp (Seq (app, cont)) 49 in
  assert_equal (mk_exp_with_annot (While (condition, body)) 0 [{atype = Invariant; aformula = "#cScope = [#lg]"}]) exp 
  
let test_continue_label () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "test: while (a > 5) {/** @invariant #cScope = [#lg] */ a++; continue test}" in
  let a = mk_exp (Var "a") 13 in
  let five = mk_exp (Num 5.0) 17 in
  let condition = mk_exp (BinOp (a, Comparison Gt, five)) 13 in
  let a = mk_exp (Var "a") 55 in
  let app = mk_exp (Unary_op (Post_Incr, a)) 55 in
  let cont = mk_exp (Continue (Some "test")) 60 in
  let body = mk_exp (Seq (app, cont)) 55 in
  let loop = mk_exp_with_annot (While (condition, body)) 6 [{atype = Invariant; aformula = "#cScope = [#lg]"}] in
  assert_equal (mk_exp (Label ("test", loop)) 0) exp
  
let test_break () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "while (a > 5) {/** @invariant #cScope = [#lg] */ a++; break}" in
  let a = mk_exp (Var "a") 7 in
  let five = mk_exp (Num 5.0) 11 in
  let condition = mk_exp (BinOp (a, Comparison Gt, five)) 7 in
  let a = mk_exp (Var "a") 49 in
  let app = mk_exp (Unary_op (Post_Incr, a)) 49 in
  let cont = mk_exp (Break None) 54 in
  let body = mk_exp (Seq (app, cont)) 49 in
  assert_equal (mk_exp_with_annot (While (condition, body)) 0 [{atype = Invariant; aformula = "#cScope = [#lg]"}]) exp 
  
let test_break_label () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "test: while (a > 5) {/** @invariant #cScope = [#lg] */ a++; break test}" in
  let a = mk_exp (Var "a") 13 in
  let five = mk_exp (Num 5.0) 17 in
  let condition = mk_exp (BinOp (a, Comparison Gt, five)) 13 in
  let a = mk_exp (Var "a") 55 in
  let app = mk_exp (Unary_op (Post_Incr, a)) 55 in
  let cont = mk_exp (Break (Some "test")) 60 in
  let body = mk_exp (Seq (app, cont)) 55 in
  let loop = mk_exp_with_annot (While (condition, body)) 6 [{atype = Invariant; aformula = "#cScope = [#lg]"}] in
  assert_equal (mk_exp (Label ("test", loop)) 0) exp
  
let test_get_invariant () =
  let xml = " <WHILE pos=\"0\">
						    <GT pos=\"7\">
						      <NAME pos=\"7\" value=\"a\"/>
						      <NUMBER pos=\"11\" value=\"5.0\"/>
						    </GT>
						    <BLOCK pos=\"14\">
						      <EXPR_RESULT pos=\"49\">
						        <INC decpos=\"post\" pos=\"49\">
						          <ANNOTATION formula=\"#cScope = [#lg]\" pos=\"49\" type=\"invariant\"/>
						          <NAME pos=\"49\" value=\"a\"/>
						        </INC>
						      </EXPR_RESULT>
						      <CONTINUE pos=\"54\"/>
						    </BLOCK>
						  </WHILE>" in
  let xml = Xml.parse_string xml in
  assert_equal [{atype = Invariant; aformula = "#cScope = [#lg]"}] (Parser.get_invariant xml)
  
let test_try_catch () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "try {a} catch (b) {c}" in
  let a = mk_exp (Var "a") 5 in
  let c = mk_exp (Var "c") 19 in
  assert_equal (mk_exp (Try (a, Some ("b", c), None)) 0) exp
  
let test_try_catch_finally () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "try {a} catch (b) {c} finally {d}" in
  let a = mk_exp (Var "a") 5 in
  let c = mk_exp (Var "c") 19 in
  let d = mk_exp (Var "d") 31 in
  assert_equal (mk_exp (Try (a, Some ("b", c), Some d)) 0) exp
  
let test_try_finally () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "try {a} finally {d}" in
  let a = mk_exp (Var "a") 5 in
  let d = mk_exp (Var "d") 17 in
  assert_equal (mk_exp (Try (a, None, Some d)) 0) exp
  
let test_switch () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "switch (a) { case 1 : b; break; default : d; case 2 : c }" in
  let a = mk_exp (Var "a") 8 in
  let one = mk_exp (Num 1.0) 18 in
  let b = mk_exp (Var "b") 22 in
  let break = mk_exp (Break None) 25 in
  let seq = mk_exp (Seq (b, break)) 22 in
  let d = mk_exp (Var "d") 42 in
  let two = mk_exp (Num 2.0) 50 in
  let c = mk_exp (Var "c") 54 in
  assert_equal (mk_exp (Switch (a, [(Case one, seq); (DefaultCase, d); (Case two, c)])) 0) exp
  
let test_debugger () =
  Symb_execution.initialize ();
  let exp = make_exp_from_string "debugger" in
  assert_equal (mk_exp Debugger 0) exp

let suite = "Testing_Parser" >:::
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
   "test_forin" >:: test_forin;
   "test_mod" >:: test_mod;
   "test_ursh" >:: test_ursh;
   "test_lsh" >:: test_lsh;
   "test_rsh" >:: test_rsh;
   "test_bitand" >:: test_bitand;
   "test_bitor" >:: test_bitor;
   "test_bitxor" >:: test_bitxor;
   "test_notequal" >:: test_notequal;
   "test_gt" >:: test_gt;
   "test_in" >:: test_in;
   "test_comma1" >:: test_comma1;
   "test_comma2" >:: test_comma2;
   "test_negative" >:: test_negative;
   "test_bitnot" >:: test_bitnot;
   "test_void" >:: test_void;
   "test_assign_add" >:: test_assign_add;
   "test_assign_sub" >:: test_assign_sub;
   "test_assign_mul" >:: test_assign_mul;
   "test_assign_div" >:: test_assign_div;
   "test_assign_mod" >:: test_assign_mod;
   "test_assign_ursh" >:: test_assign_ursh;
   "test_assign_lsh" >:: test_assign_lsh;
   "test_assign_rsh" >:: test_assign_rsh;
   "test_assign_bitand" >:: test_assign_bitand;
   "test_assign_bitor" >:: test_assign_bitor;
   "test_assign_bitxor" >:: test_assign_bitxor;
   "test_return" >:: test_return;
   "test_return_exp" >:: test_return_exp;
   "test_do_while" >:: test_do_while;
   "test_delete" >:: test_delete;
   "test_continue" >:: test_continue;
   "test_continue_label" >:: test_continue_label;
   "test_break" >:: test_break;
   "test_break_label" >:: test_break_label;
   "test_get_invariant" >:: test_get_invariant;
   "test_try_catch" >:: test_try_catch;
   "test_try_catch_finally" >:: test_try_catch_finally;
   "test_try_finally" >:: test_try_finally;
   "test_switch" >:: test_switch;
   "test_debugger" >:: test_debugger;
  ]