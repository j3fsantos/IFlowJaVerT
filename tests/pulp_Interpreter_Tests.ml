(* ./tests/pulp_Interpreter_Tests.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open OUnit
open Pulp_Syntax
open Pulp_Translate
open Pulp_Syntax_Utils
open Pulp_Syntax_Print
open Pulp_Procedure
open Interpreter
open Interpreter_Print
open Memory_Model

let get_expr p level = 
  Config.apply_config ();
  Parser_main.verbose := true;
  let exp = Parser_main.exp_from_string p in
  let _ = Printf.printf "%s \n" (Pretty_print.string_of_exp_syntax exp.Parser_syntax.exp_stx) in
  let p_exp, env = exp_to_pulp level exp main_fun_id [] in
  let _ = AllFunctions.iter (fun fid fwc -> Printf.printf "%s \n\n" (Pulp_Syntax_Print.string_of_func_block fwc)) p_exp in
  p_exp, env
  
let test_template p =
  let p_exp, env = get_expr p IVL_goto_unfold_functions in
  
  (*let cfg = Control_Flow.mk_cfg p_exp ("tests/dot/interpreter/"^name) in
	let cfg_bbs = AllFunctions.mapi (fun name cfg ->
	let fb = AllFunctions.find name p_exp in
	let cfg_bb = Simp_Main.basic_block_simplifications cfg fb.func_ctx in
	let stmts = Basic_Blocks.cfg_to_fb cfg_bb fb.func_ctx.label_throw fb.func_ctx.label_return in
	Printf.printf "Procedure %s \n %s \n" name (Pulp_Syntax_Print.string_of_statement_list stmts);
	cfg_bb
	) cfg in
  
  Basic_Blocks.print_cfg_bb cfg_bbs ("tests/dot/interpreter/bb/"^name);*)
	let builtins = env in 
  Interpreter.run_with_initial_heap p_exp builtins
  
let test_template_simp p =
  let p_exp, env = get_expr p IVL_goto in
  let p_exp = Simp_Main.simplify p_exp Simp_Common.Simp_Unfold_Specs in
	let builtins = env in 
  let env = Simp_Main.simplify builtins Simp_Common.Simp_Unfold_Specs in
  let _ = AllFunctions.iter (fun fid fwc -> Printf.printf "%s \n\n" (Pulp_Syntax_Print.string_of_func_block fwc)) p_exp in
  Interpreter.run_with_initial_heap p_exp env
  
let test_template_no_simplifications p expected_value = 
  let result = test_template p in
  assert_bool ("Incorrect Interpreter. Expected : Normal, Got Exception") (FTReturn = result.fs_return_type);
  assert_bool ("Incorrect Interpreter. Expected :" ^ (string_of_value expected_value) ^ " Actual: " ^ (string_of_value result.fs_return_value)) (value_eq expected_value ((result.fs_return_value)))
  
let test_template_normal p expected_value =
   test_template_no_simplifications p expected_value;
   
 (* by uncommenting the following 3 lines you also run the tests using simplifications *)
  let result = test_template_simp p in
  assert_bool ("Incorrect Interpreter. Expected : Normal, Got Exception") (FTReturn = result.fs_return_type);
  assert_bool ("Incorrect Interpreter. Expected :" ^ (string_of_value expected_value) ^ " Actual: " ^ (string_of_value result.fs_return_value)) (value_eq expected_value ((result.fs_return_value)))
  
 
let get_actual_excep result =
  let actual_excep_l = match result.fs_return_value with
    | VHValue (HVObj l) -> l
    | _ -> assert_failure ("An exception must be an object. Actual: " ^ (string_of_value result.fs_return_value)) in
  let actual_excep_obj = Heap.find actual_excep_l result.fs_heap in
  let actual_excep_proto = Object.find (string_of_builtin_field FProto) actual_excep_obj in
  match actual_excep_proto with
    | HVObj (BLoc l) -> l
    | _ -> assert_failure "An exception must be a builtin object"
  
let test_template_exception p expected_excep =
  let result = test_template p in
  let actual_excep = get_actual_excep result in
  assert_bool ("Incorrect Interpreter. Expected : Normal, Got Exception") (FTException = result.fs_return_type);
  assert_bool ("Incorrect Interpreter. Expected Exception :" ^ (string_of_builtin_loc expected_excep) ^ " Actual: " ^ (string_of_builtin_loc actual_excep)) (expected_excep = actual_excep);
  
  let result = test_template_simp p in
  let actual_excep = get_actual_excep result in
  assert_bool ("Incorrect Interpreter. Expected : Normal, Got Exception") (FTException = result.fs_return_type);
  assert_bool ("Incorrect Interpreter. Expected Exception :" ^ (string_of_builtin_loc expected_excep) ^ " Actual: " ^ (string_of_builtin_loc actual_excep)) (expected_excep = actual_excep)

let test_template_exception_any p expected_value =
  let result = test_template p in
  assert_bool ("Incorrect Interpreter. Expected : Normal, Got Exception") (FTException = result.fs_return_type);
  assert_bool ("Incorrect Interpreter. Expected :" ^ (string_of_value expected_value) ^ " Actual: " ^ (string_of_value result.fs_return_value)) (value_eq expected_value ((result.fs_return_value)));
  
  let result = test_template_simp p in
  assert_bool ("Incorrect Interpreter. Expected : Normal, Got Exception") (FTException = result.fs_return_type);
  assert_bool ("Incorrect Interpreter. Expected :" ^ (string_of_value expected_value) ^ " Actual: " ^ (string_of_value result.fs_return_value)) (value_eq expected_value ((result.fs_return_value)))
      
let test_program1 () = 
  test_template_normal "1" (VHValue (HVLiteral (Num 1.0)))
  
  
let test_program2 () = 
  test_template_normal "var x = 2; x" (VHValue (HVLiteral (Num 2.0)))
  
let test_program3 () =
  test_template_normal ("var x = {}; x.a = 1; x.b = 2; x.a + x.b") (VHValue (HVLiteral (Num 3.0)))
  
let test_program4 () =
  test_template_normal ("var s = function (n) { 
   var t = function (m) { 
      return {x : n} 
    }; 
   var d = t(n); 
   return d 
}; 

var r = s(3).x; r") (VHValue (HVLiteral (Num 3.0)))

let test_program5 () = 
  test_template_exception "var x = 2; y" Lrep
  
let test_program6 () =
  test_template_exception ("var a = function () { 
   var b = function () { 
      c 
    }; 
   var d = t() 
}; 

s()") Lrep

let test_if () =
  test_template_normal ("var x = 1; if (false) {x = 2}; x") (VHValue (HVLiteral (Num 1.0)))
  
let test_undefined () =
  test_template_normal ("1; var x = undefined;") (VHValue (HVLiteral (Num 1.0)))
  
let test_exception () = 
  test_template_exception "y; 1" Lrep
  
let test_program_try1 () =
  test_template_normal ("var x = 5; var f = function () {
    try {return x} catch (e) {} finally {x=7}; x = 8 
  }; f(); x") (VHValue (HVLiteral (Num 7.0)))
  
let test_program_try2 () =
  test_template_normal ("var x = 5; var f = function () {
    try {return x} catch (e) {} finally {x=7}; x = 8 
  }; var y = f(); y") (VHValue (HVLiteral (Num 5.0)))
  
let test_program_try3 () =
  test_template_normal ("var x = 5; var f = function () {
    try {} catch (e) {} finally {x=7}; x = 8 
  }; f(); x") (VHValue (HVLiteral (Num 8.0)))
  
let test_program_try4 () =
  test_template_normal ("var x = 5; var f = function () {
    try {y} catch (e) {x = 6} finally {}; 
  }; f(); x") (VHValue (HVLiteral (Num 6.0)))
  
 let test_program_try5 () =
  test_template_normal ("var x = 5; var f = function () {
    try {} catch (e) {y} finally {}; 
  }; f(); x") (VHValue (HVLiteral (Num 5.0)))
  
 let test_program_try6 () =
  test_template_exception ("var x = 5; var f = function () {
    try {y} catch (e) {y} finally {}; 
  }; f();") Lrep
  
 let test_program_try7 () =
  test_template_exception ("var x = 5; var f = function () {
    try {} catch (e) {} finally {y}; 
  }; f();") Lrep
  
let test_program_try8 () =
  test_template_normal ("var x = 5; var f = function () {
    try {return x} catch (e) {}; x = 8 
  }; f(); x") (VHValue (HVLiteral (Num 5.0)))
  
let test_program_try9 () =
  test_template_normal ("var x = 5; var f = function () {
    try {return x} finally {x=7}; x = 8 
  }; var y = f(); y") (VHValue (HVLiteral (Num 5.0)))
  
let test_program_try10 () =
  test_template_normal ("var x = 5; var f = function () {
    try {} catch (e) {}; x = 8 
  }; f(); x") (VHValue (HVLiteral (Num 8.0)))
  
let test_program_try11 () =
  test_template_exception ("var x = 5; var f = function () {
    try {y} finally {}; 
  }; f(); x") Lrep
  
 let test_program_try12 () =
  test_template_normal ("var x = 5; var f = function () {
    try {} catch (e) {y}; 
  }; f(); x") (VHValue (HVLiteral (Num 5.0)))
  
 let test_program_try13 () =
  test_template_exception ("var x = 5; var f = function () {
    try {y} catch (e) {y}; 
  }; f();") Lrep
  
 let test_program_try14 () =
  test_template_exception ("var x = 5; var f = function () {
    try {} finally {y}; 
  }; f();") Lrep
  
 let test_throw () =
  test_template_exception_any ("throw 3") (VHValue (HVLiteral (Num 3.0)))
  
 let test_strict_equal () =
  test_template_normal ("1 === 1") (VHValue (HVLiteral (Bool true)))
  
 let test_strict_not_equal () =
  test_template_normal ("1 !== 1") (VHValue (HVLiteral (Bool false)))
  
 let test_equal () =
  (* TODO conversions *)
  test_template_normal ("1 == 1") (VHValue (HVLiteral (Bool true)))
  
 let test_not_equal () =
  (* TODO conversions *)
  test_template_normal ("1 != 1") (VHValue (HVLiteral (Bool false)))
  
 let test_lt () =
  (* TODO conversions *)
  test_template_normal ("1 < 1") (VHValue (HVLiteral (Bool false)))
  
 let test_le () =
  (* TODO conversions *)
  test_template_normal ("1 <= 1") (VHValue (HVLiteral (Bool true)))
  
 let test_gt () =
  (* TODO conversions *)
  test_template_normal ("2 > 1") (VHValue (HVLiteral (Bool true)))
  
 let test_ge () =
  (* TODO conversions *)
  test_template_normal ("2 >= 1") (VHValue (HVLiteral (Bool true)))
  
 let test_assign_plus () =
  (* TODO conversions *)
  test_template_normal ("var x = 1; x += 1; x") (VHValue (HVLiteral (Num 2.0)))
  
 let test_assign_minus () =
  (* TODO conversions *)
  test_template_normal ("var x = 2; x -= 1; x") (VHValue (HVLiteral (Num 1.0)))
  
 let test_assign_div () =
  (* TODO conversions *)
  test_template_normal ("var x = 4; x /= 2; x") (VHValue (HVLiteral (Num 2.0)))
  
 let test_assign_mult () =
  (* TODO conversions *)
  test_template_normal ("var x = 2; x *= 2; x") (VHValue (HVLiteral (Num 4.0)))
  
 let test_positive () =
  (* TODO conversions *)
  test_template_normal ("var x = 2; +x") (VHValue (HVLiteral (Num 2.0)))
  
 let test_negative () =
  (* TODO conversions *)
  test_template_normal ("var x = 2; -x") (VHValue (HVLiteral (Num (-.2.0))))
  
 let test_mod () =
  test_template_normal ("var x = 5; x % 2") (VHValue (HVLiteral (Num 1.0)))
  
 let test_assign_mod () =
  (* TODO conversions *)
  test_template_normal ("var x = 6; x %= 4; x") (VHValue (HVLiteral (Num 2.0)))
  
 let test_assign_void () =
  (* TODO conversions *)
  test_template_normal ("var x; void (x = 6)") (VHValue (HVLiteral Undefined)) 
  
 let test_assign_void_expr () =
  (* TODO conversions *)
  test_template_normal ("var x; void (x = 6); x") (VHValue (HVLiteral (Num 6.0))) 
  
 let test_pre_inc () =
  test_template_normal ("var x = 1; ++x") (VHValue (HVLiteral (Num 2.0))) 
  
 let test_pre_dec () =
  test_template_normal ("var x = 2; --x") (VHValue (HVLiteral (Num 1.0)))
  
 let test_post_inc () =
  test_template_normal ("var x = 3; x++") (VHValue (HVLiteral (Num 3.0))) 
  
 let test_post_dec () =
  test_template_normal ("var x = 4; x--;") (VHValue (HVLiteral (Num 4.0)))
  
 let test_post_inc_after () =
  test_template_normal ("var x = 3; x++; x") (VHValue (HVLiteral (Num 4.0))) 
  
 let test_post_dec_after () =
  test_template_normal ("var x = 4; x--; x") (VHValue (HVLiteral (Num 3.0)))
  
 let test_function_decl_1 () =
   test_template_normal ("function f () {return 5}; f()") (VHValue (HVLiteral (Num 5.0)))
  
 let test_function_decl_2 () =
   test_template_normal ("f(); function f () {return 5};") (VHValue (HVLiteral (Num 5.0)))
  
 let test_eval_1 () =
   test_template_normal ("eval ('1')") (VHValue (HVLiteral (Num 1.0)))
  
 let test_do_while () =
   test_template_normal ("var x = 1; do { x++ } while (x < 4)") (VHValue (HVLiteral (Num 3.0)))
  
 let test_conditional_expr_true () =
   test_template_normal ("var x = 1; (x === 1 ? 'one' : 'not one')") (VHValue (HVLiteral (String "one")))
 
 let test_conditional_expr_false () =
   test_template_normal ("var x = 2; (x === 1 ? 'one' : 'not one')") (VHValue (HVLiteral (String "not one")))
  
 let test_comma () =
   test_template_normal ("(1, 2)") (VHValue (HVLiteral (Num 2.0)))
 
 let test_comma_after () =
   test_template_normal ("var y = 1; (y++, 1); y") (VHValue (HVLiteral (Num 2.0)))
  
let test_cav_example_1 () =
  test_template_normal ("var object = {
 property: 'some property',
 method: function() {
   return this.property;
 }
};

object.method()") (VHValue (HVLiteral (String "some property")))

let test_cav_example_2 () =
  test_template_exception ("var object = {
 property: 'some property',
 method: function() {
   return this.property;
 }
};

var f = object.method;
f() ") Ltep

let test_cav_example_3 () =
  test_template_normal ("var MyObject = function(p) {
    this.property = p;
    this.method = function() {
      return this.property;
    }
};

var obj = new MyObject('some property');
obj.method();") (VHValue (HVLiteral (String "some property")))

let test_cav_example_4 () =
  test_template_exception ("var MyObject = function(p) {
    this.property = p;
    this.method = function() {
      return this.property;
    }
};

var obj = new MyObject('some property');
var f = obj.method;
f()") Ltep

let test_cav_example_5 () =
  test_template_normal ("
  var prop = 'global property';
  var object = {
 prop: 'some property',
 method: function() {
   return this.prop === prop;
 }
};


object.method()") (VHValue (HVLiteral (Bool false)))

let test_cav_example_6 () =
  test_template_exception ("
  var prop = 'global property';
  var object = {
 prop: 'some property',
 method: function() {
   return this.prop === prop;
 }
};

var f = object.method;
f()") Ltep 

let test_instance_of_true () =
  test_template_normal ("function C(){}; function D(){}; var o = new C(); o instanceof C")
  (VHValue (HVLiteral (Bool true)))
  
let test_instance_of_false () =
  test_template_normal ("function C(){}; function D(){}; var o = new C(); o instanceof D")
  (VHValue (HVLiteral (Bool false)))
  
let test_in_true () =
  test_template_normal ("var x = {a : 1, b : 2}; 'a' in x ")
  (VHValue (HVLiteral (Bool true)))
  
let test_in_false () =
  test_template_normal ("var x = {a : 1, b : 2}; 'c' in x ")
  (VHValue (HVLiteral (Bool false)))
  
let test_type_of_undefined () =
  test_template_normal ("typeof undefined") (VHValue (HVLiteral (String "undefined")))
  
let test_type_of_bool () =
  test_template_normal ("typeof true") (VHValue (HVLiteral (String "boolean")))
  
let test_type_of_string () =
  test_template_normal ("typeof 'a'") (VHValue (HVLiteral (String "string")))
  
let test_type_of_number () =
  test_template_normal ("typeof 1") (VHValue (HVLiteral (String "number")))
  
let test_type_of_null () =
  test_template_normal ("typeof null") (VHValue (HVLiteral (String "object")))
    
let test_type_of_object () =
  test_template_normal ("var x = {}; typeof x") (VHValue (HVLiteral (String "object")))
  
let test_type_of_function () =
  test_template_normal ("function x () {}; typeof x") (VHValue (HVLiteral (String "function")))
  
let test_type_of_undefined_ref () =
  test_template_normal ("typeof x") (VHValue (HVLiteral (String "undefined")))
  
let test_named_function () =
  test_template_normal ("var f = function m (x) {
    if (x === 0) return 0;
    if (x === 1) return 1;
    return m(x-2) + m(x-1);
};

f(4)") (VHValue (HVLiteral (Num 3.0)))

let test_to_num_1 () =
  test_template_normal ("2 * '4'") (VHValue (HVLiteral (Num 8.0)))
  
let test_plus_string () =
  test_template_normal ("2 + '5'") (VHValue (HVLiteral (String "25")))
  
let test_plus_num () =
  test_template_normal ("2 + 5") (VHValue (HVLiteral (Num 7.0)))
  
let test_boolean_call () =
  test_template_normal ("Boolean('true')") (VHValue (HVLiteral (Bool true)))
  
let test_boolean_construct () =
  test_template_normal ("typeof (new Boolean('true'))") (VHValue (HVLiteral (String "object")))
  
let test_object_construct () =
  test_template_normal ("var x = new Object(); x.toString()") (VHValue (HVLiteral (String "[object Object]")))
  
let test_object_construct_value () =
  test_template_normal ("var n_obj = new Object(function func(){return 1;}); n_obj ()") (VHValue (HVLiteral (Num 1.0)))
  
let test_plus_to_primitive_boolean () =
  test_template_normal ("'' + (new Boolean('true'))") (VHValue (HVLiteral (String "true")))
  
let test_S11_9_4_A2_4_T1 () =
  test_template_normal ("var x = 0; (x === (x = 1))") (VHValue (HVLiteral (Bool false)))
  
let test_S11_9_1_A3_3__1 () =
  test_template_normal ("(0 == false) !== true") (VHValue (HVLiteral (Bool false)))
  
let test_S11_9_1_A3_3__2 () =
  test_template_normal ("('1' == true) !== true") (VHValue (HVLiteral (Bool false)))
  
let test_S11_9_1_A7_8 () =
   test_template_normal ("({valueOf: function() {return 1}} == true) !== true") (VHValue (HVLiteral (Bool false)))
  
let test_plus_to_primitive_number () =
  test_template_normal ("5 + (new Number('2'))") (VHValue (HVLiteral (Num 7.)))
  
let test_plus_to_primitive_string () =
  test_template_normal ("6 + (new String(7))") (VHValue (HVLiteral (String "67")))
  
let test_S15_6_4_3_A2_T4 () =
   test_template_normal ("try{
     var s1 = new Object();
     s1.valueOf = Boolean.prototype.valueOf;
     var v1 = s1.valueOf(); 
     }
    catch(e){
      e instanceof TypeError
     }") (VHValue (HVLiteral (Bool true)))
  
let test_S8_5_A5 () =
  test_template_normal ("var x = NaN; var x_leq_0=(x <= 0.0); x_leq_0") (VHValue (HVLiteral (Bool false))) 
  
let test_S11_13_2_A3_2_T9 () =
  test_template_normal ("var x = 1; var x1 = (x &= 1); x1") (VHValue (HVLiteral (Num 1.))) 
  
let test_S9_5_A2_3_T1 () =
  test_template_normal ("(2147483647 << 0) === 2147483647") (VHValue (HVLiteral (Bool true))) 
  
let test_S15_2_2_1_A5_T2 () =
  test_template_normal ("var num = NaN; var n_obj = new Object(num); n_obj.constructor === Number") (VHValue (HVLiteral (Bool true))) 
  
let test_S11_9_2_A7_8 () =
  test_template_normal ("try {
  (1 != {valueOf: function() {return {}}, toString: function() {return {}}})
}  
catch (e) {
  e instanceof TypeError 
}") (VHValue (HVLiteral (Bool true)))

let test_S8_7_1_A1 () =
  test_template_normal ("this.y = 1; delete this.y; this.y") (VHValue (HVLiteral Undefined))
  
let test_S15_6_4_A2 () =
  test_template_normal ("!Object.prototype.isPrototypeOf(Boolean.prototype)") (VHValue (HVLiteral (Bool false)))
  
let test_get_prototype_of () =
  test_template_normal ("Object.getPrototypeOf(Boolean)") (VHValue (HVObj (BLoc Lfp)))
  
let test_S11_4_1_A3_3 () =
  test_template_normal ("try { x = 1; delete x; x} catch (e) {e instanceof ReferenceError}") (VHValue (HVLiteral (Bool true)))
  
let test_11_2_3_3_5 () =
  test_template_normal (
    " function testcase() {
      var fooCalled = false;
      function foo(){ fooCalled = true; } 
    
      var o = { }; 
      try {
        eval('o.bar( foo() );');
        throw new Exception('o.bar does not exist!');
      } catch(e) {
        return (e instanceof TypeError) && (fooCalled===true);
      }
    };
    testcase();") (VHValue (HVLiteral (Bool true)))
    
let test_S15_2_4_6_A6 () =
  test_template_normal ("Object.prototype.isPrototypeOf.prototype") (VHValue (HVLiteral Undefined))
  
let test_S15_7_4_4_A2_T05 () =
  test_template_normal ("try{
  var s1 = {x: 1};
  s1.valueOf = Number.prototype.valueOf;
  var v1 = s1.valueOf(); 
}
catch(e){
  e instanceof TypeError
}") (VHValue (HVLiteral (Bool true)))

let test_S15_6_4_3_A1_T2 () =
  test_template_normal ("Boolean.prototype.valueOf(true)") (VHValue (HVLiteral (Bool false)))
  
let test_S8_12_3_A3 () =
  test_template_normal ("var __map={shape:'cube', 5:'five', '6':'six'}; __map['5']") (VHValue (HVLiteral (String "five")))
  
let test_S11_9_2_A4_1_T1 () =
  test_template_normal ("Number.NaN != \"string\"") (VHValue (HVLiteral (Bool true)))
  
let test_S11_10_3_A3_T1_5 () =
  test_template_normal ("({} | function(){return 1})") (VHValue (HVLiteral (Num 0.)))
  
let test_S11_11_2_A3_T2 () =
  test_template_normal ("(0 || -0)") (VHValue (HVLiteral (Num 0.)))
  
let test_S11_8_4_A3_1_T2_4 () =
  test_template_normal ("undefined >= new Number(1)") (VHValue (HVLiteral (Bool false)))
  
let test_do_while_break () =
   test_template_normal ("var x = 1; do { if (x == 4) {break}; x++ } while (x < 10)") (VHValue (HVLiteral (Num 3.0)))
  
let test_is_nan_false () =
  test_template_normal ("isNaN (1)") (VHValue (HVLiteral (Bool false)))
  
let test_is_nan_true () =
  test_template_normal ("isNaN (NaN)") (VHValue (HVLiteral (Bool true)))
  
let test_is_finite_false () =
  test_template_normal ("isFinite (Infinity)") (VHValue (HVLiteral (Bool false)))
  
let test_is_finite_true () =
  test_template_normal ("isFinite (7)") (VHValue (HVLiteral (Bool true)))
  
let test_negative_nan () =
  test_template_normal ("isNaN(-{})") (VHValue (HVLiteral (Bool true)))
 
(* TODO *)
  
let test_while_break () =
  test_template_normal ("var x = 2; while(true) {x++; break; 1}") (VHValue (HVLiteral (Num 2.)))
  
let test_while_false () =
  test_template_normal "var __in__do; while ( false ) __in__do=1; __in__do" (VHValue (HVLiteral Undefined))
  
let test_ () =
  test_template_normal " // CHECK#3
try{
  throw \"ex1\";
}
catch(er1){
  if (er1!==\"ex1\") $ERROR('#3.1: Exception ===\"ex1\". Actual:  Exception ==='+ er1  );
}
finally{
  try{
    throw \"ex2\";
  }
  catch(er1){

  }
}
" (VHValue (HVLiteral (Bool true)))

let test_program_switch_aux () =
  test_template_normal ("
		switch(0) { }")  (VHValue (HVLiteral Empty))


let test_program_switch1 () =
  test_template_normal ("var x1;
	  var x2; 
		var x3; 
		var x4;
		var x5; 
		var i; 
		i = 0;
		x1 = 1; 
		x2 = 1; 
		x3 = 1; 
		x4 = 1;
		x5 = 1; 
		switch(i) { 
			 case 0: x1 = 2
			 case 1: x2 = 3 
			 default: x3 = 5
			case 2: x4 = 7
			case 3: x5 = 11
		} 
		x1 * x2 * x3 * x4 * x5")  (VHValue (HVLiteral (Num 2310.0)))

let test_program_switch2 () =
  test_template_normal ("var x1;
	  var x2; 
		var x3; 
		var x4;
		var x5; 
		var i; 
		i = 1;
		x1 = 1; 
		x2 = 1; 
		x3 = 1; 
		x4 = 1;
		x5 = 1; 
		switch(i) { 
			 case 0: x1 = 2
			 case 1: x2 = 3 
			 default: x3 = 5
			case 2: x4 = 7
			case 3: x5 = 11
		} 
		x1 * x2 * x3 * x4 * x5")  (VHValue (HVLiteral (Num 1155.0)))

let test_program_switch3 () =
  test_template_normal ("var x1;
	  var x2; 
		var x3; 
		var x4;
		var x5; 
		var i; 
		i = 2;
		x1 = 1; 
		x2 = 1; 
		x3 = 1; 
		x4 = 1;
		x5 = 1; 
		switch(i) { 
			 case 0: x1 = 2
			 case 1: x2 = 3 
			 default: x3 = 5
			case 2: x4 = 7
			case 3: x5 = 11
		} 
		x1 * x2 * x3 * x4 * x5")  (VHValue (HVLiteral (Num 77.0)))
	
let test_program_switch4 () =
  test_template_normal ("var x1;
	  var x2; 
		var x3; 
		var x4;
		var x5; 
		var i; 
		i = 3;
		x1 = 1; 
		x2 = 1; 
		x3 = 1; 
		x4 = 1;
		x5 = 1; 
		switch(i) { 
			 case 0: x1 = 2
			 case 1: x2 = 3 
			 default: x3 = 5
			case 2: x4 = 7
			case 3: x5 = 11
		} 
		x1 * x2 * x3 * x4 * x5")  (VHValue (HVLiteral (Num 11.0)))		

let test_program_switch5 () =
  test_template_normal ("var x1;
	  var x2; 
		var x3; 
		var x4;
		var x5; 
		var i; 
		i = 4;
		x1 = 1; 
		x2 = 1; 
		x3 = 1; 
		x4 = 1;
		x5 = 1; 
		switch(i) { 
			 case 0: x1 = 2
			 case 1: x2 = 3 
			 default: x3 = 5
			case 2: x4 = 7
			case 3: x5 = 11
		} 
		x1 * x2 * x3 * x4 * x5")  (VHValue (HVLiteral (Num 385.0)))		
		
 let test_program_switch6 () =
  test_template_normal ("var x1, x2, x3, x4, x5; 
		var i; 
		i = 0;
		switch(i) { 
			 case 0: x1 = 2; break;
			 case 1: x2 = 3 
			 default: x3 = 5
			case 2: x4 = 7
			case 3: x5 = 11
		}")  (VHValue (HVLiteral (Num 2.0)))		

 let test_program_switch7 () =
  test_template_normal ("var x1, x2, x3, x4, x5; 
		var i; 
		i = 1;
		switch(i) { 
			 case 0: x1 = 2; 
			 case 1: x2 = 3; break;  
			 default: x3 = 5
			case 2: x4 = 7
			case 3: x5 = 11
		}")  (VHValue (HVLiteral (Num 3.0)))		

 let test_program_switch8 () =
  test_template_normal ("var x1, x2, x3, x4, x5; 
		var i; 
		i = 2;
		switch(i) { 
			 case 0: x1 = 2
			 case 1: x2 = 3 
			 default: x3 = 5
			case 2: x4 = 7; break; 
			case 3: x5 = 11
		}")  (VHValue (HVLiteral (Num 7.0)))				
 
 let test_program_switch9 () =
  test_template_normal ("var x1, x2, x3, x4, x5; 
		var i; 
		i = 3;
		switch(i) { 
			 case 0: x1 = 2
			 case 1: x2 = 3 
			 default: x3 = 5
			case 2: x4 = 7;  
			case 3: x5 = 11
		}")  (VHValue (HVLiteral (Num 11.0)))				
																

let test_program_switch10 () =
  test_template_normal ("var x1, x2, x3, x4, x5; 
		var i; 
		i = 4;
		switch(i) { 
			 case 0: x1 = 2
			 case 1: x2 = 3 
			 default: x3 = 5; 
			case 2: x4 = 7;  
			case 3: x5 = 11
		}")  (VHValue (HVLiteral (Num 11.0)))				

let test_if_completion_1 () =
  test_template_normal ("var x, y;
	  x = 1; 
		y = 0; 
		if (x) { 
			y = 3
	  } else {
			y = 4
	 }")  (VHValue (HVLiteral (Num 3.0)))

let test_if_completion_2 () =
  test_template_normal ("var x, y;
	  x = 0; 
		if (x) { 
			y = 3
	  } else {
			y = 4
	 }")  (VHValue (HVLiteral (Num 4.0)))

let test_while_completion_1 () =
  test_template_normal ("var x; 
		while (2) { x = 3; break }")  (VHValue (HVLiteral (Num 3.0)))		

let test_while_completion_2 () =
  test_template_normal ("var x, y; 
	  x = 0; 
		y = 0;
		while (x < 4) { y += x; x += 1; }")  (VHValue (HVLiteral (Num 4.0)))	

let test_do_while_completion_1 () =
  test_template_normal ("var x; 
		do { x = 3; break } while (true)")  (VHValue (HVLiteral (Num 3.0)))		

let test_do_while_completion_2 () =
  test_template_normal ("var x, y; 
	  x = 0; 
		y = 0;
		do { y += x; x += 1; } while (x < 4)")  (VHValue (HVLiteral (Num 4.0)))	

let test_for_completion_1 () =
  test_template_normal ("var x, y; 
	  x = 0; 
		y = 5;
		for (x = 0; x < y; x++) { y += 1; x += 2; }")  (VHValue (HVLiteral (Num 8.0)))	


let test_for_completion_2 () =
  test_template_normal ("var x, y; 
	  x = 0; 
		y = 5;
		for (x = 0; x < y; x++) { 
			if (x > y/2) { break }
	  }")  (VHValue (HVLiteral (Num 5.0)))

let test_try_catch_completion_1 () =
  test_template_normal ("try { 0 } finally { 1 } ")  (VHValue (HVLiteral (Num 1.0)))

let test_try_catch_completion_2 () =
  test_template_normal ("try { throw 3} catch (e) { e } ")  (VHValue (HVLiteral (Num 3.0)))
  
let test_11_2_1_A1_2 () =
  test_template_exception "var object; object[1];" Ltep
  
let test_S12_14_A10_T3 () =
  test_template_normal ("var c7=0;
try{
  while(c7<2){
    try{
      c7+=1;
      throw 'ex1';
    }
    finally{
      break;
    }
    c7+=2;
  }
}
catch(ex1){
  c7=10;
}
") (VHValue (HVLiteral (Num 1.0))) 

let test_S8_7_A4 () =
  test_template_normal ("
    var item = new String('test');
    var itemRef = item;
    item += 'ing';"
    ) (VHValue (HVLiteral (String "testing"))) 
    
let test_12_6_1_A4_T5 () =
  test_template_normal ("var i=0;
woohoo:{ 
  do{
    i++;
    if ( ! (i < 10) ) {
      break woohoo;
    }
  } while ( true );
}") (VHValue (HVLiteral (Num 9.0))) 

let test_S13_A7_T2 () =
  test_template_normal ("var r; try{
    eval('function __func(){/ ABC}');
    r = 0;
    } catch(e){
    if(!(e instanceof SyntaxError)){
      r = 1;
    }
    }") (VHValue (HVLiteral (Undefined))) 
    
let test_get_prototyte_of_empty () =
  test_template_exception ("Object.getPrototypeOf()") Ltep
  
let test_eval_this () =
  test_template_normal ("if (eval('this') !== this) {
    throw 'This had incorrect value!';
  }") (VHValue (HVLiteral (Undefined))) 

let test_12_2_1_7_s () =
  test_template_exception "eval('var eval;');" Lsep
  
let test_array_initialiser () =
  test_template_normal "var x = [5,,]; x.length " (VHValue (HVLiteral (Num 2.0)))
  
let test_array_initialiser_get_value_1 () =
  test_template_normal "var x = [,5,]; x[0] " (VHValue (HVLiteral Undefined))
  
let test_array_initialiser_get_value_2 () =
  test_template_normal "var x = [,5,]; x[1] " (VHValue (HVLiteral (Num 5.0)))
  
let test_array_initialiser_define_prop () =
  test_template_normal "var x = [,5,]; x[3] = 'test'; x[3] " (VHValue (HVLiteral (String "test")))
  
let test_array_initialiser_define_prop_length () =
  test_template_normal "var x = [,5,]; x[3] = 'test'; x.length " (VHValue (HVLiteral (Num 4.0)))
  
let test_array_initialiser_set_length_greater () =
  test_template_normal "var x = [,5,4]; x.length = 7; x.length " (VHValue (HVLiteral (Num 7.0)))
  
let test_array_initialiser_set_length_smaller () =
  test_template_normal "var x = [,5,]; x.length = 1; x[1]" (VHValue (HVLiteral (Undefined)))
  
  

let suite = "Testing_Interpreter" >:::
  [
		(*"test_program_switch_aux" >:: test_program_switch_aux;*)
	  "test_program_switch1" >:: test_program_switch1;
		"test_program_switch2" >:: test_program_switch2;
		"test_program_switch3" >:: test_program_switch3;
		"test_program_switch5" >:: test_program_switch5;
		"test_program_switch6" >:: test_program_switch6;
		"test_program_switch7" >:: test_program_switch7;
		"test_program_switch8" >:: test_program_switch8;
		"test_program_switch9" >:: test_program_switch9;
		"test_program_switch10" >:: test_program_switch10;
		"test_if_completion_1" >:: test_if_completion_1; 
		"test_if_completion_2" >:: test_if_completion_2; 
		"test_while_completion_1" >:: test_while_completion_1;
		"test_while_completion_2" >:: test_while_completion_2;
		"test_do_while_completion_1" >:: test_do_while_completion_1;
		"test_do_while_completion_2" >:: test_do_while_completion_2;
		"test_for_completion_1" >:: test_for_completion_1;
		"test_for_completion_2" >:: test_for_completion_2;
		"test_try_catch_completion_1" >:: test_try_catch_completion_1; 
		"test_try_catch_completion_2" >:: test_try_catch_completion_2;
	  "running program1" >:: test_program1;
   "running program2" >:: test_program2;
   "running_program3" >:: test_program3;
   "running_program4" >:: test_program4;
   "running_program5" >:: test_program5;
   "running_program6" >:: test_program6;
   "running_if" >:: test_if;
   "running_undefined" >:: test_undefined;
   "testing exception" >:: test_exception;
   "test_program_try1" >:: test_program_try1;
   "test_program_try2" >:: test_program_try2;
   "test_program_try3" >:: test_program_try3;
   "test_program_try4" >:: test_program_try4;
   "test_program_try5" >:: test_program_try5;
   "test_program_try6" >:: test_program_try6;
   "test_program_try7" >:: test_program_try7;
   "test_program_try8" >:: test_program_try8;
   "test_program_try9" >:: test_program_try9;
   "test_program_try10" >:: test_program_try10;
   "test_program_try11" >:: test_program_try11;
   "test_program_try12" >:: test_program_try12;
   "test_program_try13" >:: test_program_try13;
   "test_program_try14" >:: test_program_try14;
   "test_throw" >:: test_throw;
   "test_strict_equal" >:: test_strict_equal;
   "test_strict_not_equal" >:: test_strict_not_equal;
   "test_equal" >:: test_equal;
   "test_not_equal" >:: test_not_equal;
   "test_lt" >:: test_lt;
   "test_gt" >:: test_gt;
   "test_le" >:: test_le;
   "test_ge" >:: test_ge; 
   "test_assign_plus" >:: test_assign_plus;
   "test_assign_minus" >:: test_assign_minus;
   "test_assign_div" >:: test_assign_div;
   "test_assign_mult" >:: test_assign_mult;
   "test_positive" >:: test_positive;
   "test_negative" >:: test_negative;
   "test_mod" >:: test_mod;
   "test_assign_mod" >:: test_assign_mod;
   "test_assign_void" >:: test_assign_void;
   "test_assign_void_expr" >:: test_assign_void_expr;
   "test_pre_inc" >:: test_pre_inc;
   "test_pre_dec" >:: test_pre_dec; 
   "test_post_inc" >:: test_post_inc; 
   "test_post_dec" >:: test_post_dec;  
   "test_post_inc_after" >:: test_post_inc_after; 
   "test_post_dec_after" >:: test_post_dec_after; 
   "test_function_decl_1" >:: test_function_decl_1;
   "test_function_decl_2" >:: test_function_decl_2;
   "test_eval_1" >:: test_eval_1;
   "test_cav_example_1" >:: test_cav_example_1;
   "test_cav_example_2" >:: test_cav_example_2;
   "test_cav_example_3" >:: test_cav_example_3;
   "test_cav_example_4" >:: test_cav_example_4;
    "test_cav_example_5" >:: test_cav_example_5;
    "test_cav_example_6" >:: test_cav_example_6;
    "test_instance_of_true" >:: test_instance_of_true;
    "test_instance_of_false" >:: test_instance_of_false;
    "test_in_true" >:: test_in_true;
    "test_in_false" >:: test_in_false;
    "test_type_of_undefined">::test_type_of_undefined;
    "test_type_of_bool">::test_type_of_bool;
    "test_type_of_number">::test_type_of_number;
    "test_type_of_string">::test_type_of_string;
    "test_type_of_null">::test_type_of_null;
    "test_type_of_object">::test_type_of_object;
    "test_type_of_function">::test_type_of_function;
    "test_type_of_undefined_ref">::test_type_of_undefined_ref;
    "test_do_while" >:: test_do_while;
    "test_conditional_expr_true" >:: test_conditional_expr_true;
    "test_conditional_expr_false" >:: test_conditional_expr_false;
    "test_comma" >:: test_comma;
    "test_comma_after" >:: test_comma_after;
    "test_named_function" >:: test_named_function;
    "test_to_num_1" >:: test_to_num_1;
    "test_plus_string" >:: test_plus_string;
    "test_plus_num" >:: test_plus_num;
    "test_boolean_call" >:: test_boolean_call;
    "test_boolean_construct" >:: test_boolean_construct;
    "test_object_construct" >:: test_object_construct;
    "test_object_construct_value" >:: test_object_construct_value;
    "test_S11_9_4_A2_4_T1" >:: test_S11_9_4_A2_4_T1;
    "test_S11_9_1_A3_3__1" >:: test_S11_9_1_A3_3__1;
    "test_S11_9_1_A3_3__2" >:: test_S11_9_1_A3_3__2;
    "test_S11_9_1_A7_8" >:: test_S11_9_1_A7_8;
    "test_plus_to_primitive_boolean" >:: test_plus_to_primitive_boolean;
    "test_plus_to_primitive_number" >:: test_plus_to_primitive_number;
    "test_plus_to_primitive_string" >:: test_plus_to_primitive_string;
    "test_S15_6_4_3_A2_T4" >:: test_S15_6_4_3_A2_T4;
    "test_S8_5_A5" >:: test_S8_5_A5;
    "test_S11_13_2_A3_2_T9" >:: test_S11_13_2_A3_2_T9;
    "test_S9_5_A2_3_T1" >:: test_S9_5_A2_3_T1;
    "test_S15_2_2_1_A5_T2" >::test_S15_2_2_1_A5_T2;
    "test_S11_9_2_A7_8" >:: test_S11_9_2_A7_8;
    "test_S8_7_1_A1" >:: test_S8_7_1_A1;
    "test_S15_6_4_A2" >:: test_S15_6_4_A2;
    "test_get_prototype_of" >:: test_get_prototype_of;
    "test_S11_4_1_A3_3" >:: test_S11_4_1_A3_3;
    "test_11_2_3_3_5" >:: test_11_2_3_3_5;
    "test_S15_2_4_6_A6" >:: test_S15_2_4_6_A6;
    "test_S15_7_4_4_A2_T05" >:: test_S15_7_4_4_A2_T05;
    "test_S8_12_3_A3" >:: test_S8_12_3_A3; 
    "test_S11_9_2_A4_1_T1" >:: test_S11_9_2_A4_1_T1;
    "test_S11_10_3_A3_T1_5" >:: test_S11_10_3_A3_T1_5;
    "test_S11_11_2_A3_T2" >:: test_S11_11_2_A3_T2;
    "test_S11_8_4_A3_1_T2_4" >:: test_S11_8_4_A3_1_T2_4;
    "test_do_while_break" >:: test_do_while_break;
    "test_is_nan_false" >:: test_is_nan_false;
    "test_is_nan_true" >:: test_is_nan_true;
    "test_is_finite_false" >:: test_is_finite_false;
    "test_is_finite_true" >:: test_is_finite_true;
    "test_negative_nan" >:: test_negative_nan;
    "test_11_2_1_A1_2" >:: test_11_2_1_A1_2;
    "test_S12_14_A10_T3" >:: test_S12_14_A10_T3;
    "test_S8_7_A4" >:: test_S8_7_A4;
    "test_12_6_1_A4_T5" >:: test_12_6_1_A4_T5;
    "test_S13_A7_T2" >:: test_S13_A7_T2;
    "test_get_prototyte_of_empty" >:: test_get_prototyte_of_empty;
    "test_eval_this" >:: test_eval_this;
    "test_12_2_1_7_s" >:: test_12_2_1_7_s;
    "test_array_initialiser" >:: test_array_initialiser;
    "test_array_initialiser_get_value_1" >:: test_array_initialiser_get_value_1;
    "test_array_initialiser_get_value_2" >:: test_array_initialiser_get_value_2;
    "test_array_initialiser_define_prop" >:: test_array_initialiser_define_prop;
    "test_array_initialiser_define_prop_length" >:: test_array_initialiser_define_prop_length;
    "test_array_initialiser_set_length_greater" >:: test_array_initialiser_set_length_greater;
    "test_array_initialiser_set_length_smaller" >:: test_array_initialiser_set_length_smaller;
    (*"test_" >:: test_*) 
    ] 
