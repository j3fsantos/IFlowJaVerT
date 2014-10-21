open OUnit
open Pulp_Syntax
open Pulp_Translate
open Pulp_Syntax_Utils
open Pulp_Syntax_Print
open Interpreter
open Interpreter_Print
open Memory_Model

let test_template p =
  Config.apply_config ();
  Parser_main.verbose := true;
  let exp = Parser_main.exp_from_string p in
  let _ = Printf.printf "%s \n" (Pretty_print.string_of_exp_syntax exp.Parser_syntax.exp_stx) in
  let p_exp = exp_to_pulp exp in
  let _ = AllFunctions.iter (fun fid fwc -> Printf.printf "%s \n\n" (Pulp_Syntax_Print.string_of_func_block fwc)) p_exp in
  Interpreter.run_with_initial_heap p_exp
  
let test_template_normal p expected_value =
  let result = test_template p in
  assert_bool ("Incorrect Interpreter. Expected :" ^ (string_of_value expected_value) ^ " Actual: " ^ (string_of_value result.fs_return_value)) (value_eq expected_value ((result.fs_return_value))) 
  
let test_template_exception p expected_excep =
  let result = test_template p in
  let actual_excep_l = match result.fs_return_value with
    | VHValue (HVObj l) -> l
    | _ -> assert_failure "An exception must be an object" in
  let actual_excep_obj = Heap.find actual_excep_l result.fs_heap in
  let actual_excep_proto = Object.find (string_of_builtin_field FProto) actual_excep_obj in
  let actual_excep = match actual_excep_proto with
    | HVObj (BLoc l) -> l
    | _ -> assert_failure "An exception must be a builtin object" in
  assert_bool ("Incorrect Interpreter. Expected Exception :" ^ (string_of_builtin_loc expected_excep) ^ " Actual: " ^ (string_of_builtin_loc actual_excep)) (expected_excep = actual_excep)
  
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
  test_template_normal ("var x = 1; if (false) {x = 2}; x ") (VHValue (HVLiteral (Num 1.0)))
  
let suite = "Testing_Interpreter" >:::
  ["running program1" >:: test_program1;
   "running program2" >:: test_program2;
   "running_program3" >:: test_program3;
   "running_program4" >:: test_program4;
   "running_program5" >:: test_program5;
   "running_program6" >:: test_program6;
   "running_if" >:: test_if] 