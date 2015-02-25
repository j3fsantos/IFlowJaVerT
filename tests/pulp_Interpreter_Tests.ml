open OUnit
open Pulp_Syntax
open Pulp_Translate
open Pulp_Syntax_Utils
open Pulp_Syntax_Print
open Interpreter
open Interpreter_Print
open Memory_Model

let get_expr p = 
  Config.apply_config ();
  Parser_main.verbose := true;
  let exp = Parser_main.exp_from_string p in
  let _ = Printf.printf "%s \n" (Pretty_print.string_of_exp_syntax exp.Parser_syntax.exp_stx) in
  let p_exp = exp_to_pulp IVL_goto exp main_fun_id in
  let _ = AllFunctions.iter (fun fid fwc -> Printf.printf "%s \n\n" (Pulp_Syntax_Print.string_of_func_block fwc)) p_exp in
  p_exp

let test_template p =
  let p_exp = get_expr p in
  Interpreter.run_with_initial_heap p_exp
  
let test_template_simp p =
  let p_exp = get_expr p in
  let p_exp = Simp_Main.simplify p_exp in
  let _ = AllFunctions.iter (fun fid fwc -> Printf.printf "%s \n\n" (Pulp_Syntax_Print.string_of_func_block fwc)) p_exp in
  Interpreter.run_with_initial_heap p_exp
  
let test_template_normal p expected_value =
 let result = test_template p in
  assert_bool ("Incorrect Interpreter. Expected : Normal, Got Exception") (FTReturn = result.fs_return_type);
  assert_bool ("Incorrect Interpreter. Expected :" ^ (string_of_value expected_value) ^ " Actual: " ^ (string_of_value result.fs_return_value)) (value_eq expected_value ((result.fs_return_value)));
  
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
  test_template_exception "var x = 2; y" LRError
  
let test_program6 () =
  test_template_exception ("var a = function () { 
   var b = function () { 
      c 
    }; 
   var d = t() 
}; 

s()") LRError

let test_if () =
  test_template_normal ("var x = 1; if (false) {x = 2}; x") (VHValue (HVLiteral (Num 1.0)))
  
let test_undefined () =
  test_template_normal ("var x = undefined;") (VHValue (HVLiteral Empty))
  
let test_exception () = 
  test_template_exception "y; 1" LRError
  
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
  }; f();") LRError
  
 let test_program_try7 () =
  test_template_exception ("var x = 5; var f = function () {
    try {} catch (e) {} finally {y}; 
  }; f();") LRError
  
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
  }; f(); x") LRError
  
 let test_program_try12 () =
  test_template_normal ("var x = 5; var f = function () {
    try {} catch (e) {y}; 
  }; f(); x") (VHValue (HVLiteral (Num 5.0)))
  
 let test_program_try13 () =
  test_template_exception ("var x = 5; var f = function () {
    try {y} catch (e) {y}; 
  }; f();") LRError
  
 let test_program_try14 () =
  test_template_exception ("var x = 5; var f = function () {
    try {} finally {y}; 
  }; f();") LRError
  
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
f() ") LTError

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
f()") LTError

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
f()") LTError 

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
    
let suite = "Testing_Interpreter" >:::
  ["running program1" >:: test_program1;
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
    ] 