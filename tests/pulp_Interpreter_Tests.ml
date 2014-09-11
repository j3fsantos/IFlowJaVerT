open OUnit
open Pulp_Syntax
open Pulp_Translate
open Pulp_Syntax_Utils
open Interpreter
open Interpreter_Print

let test_template p name expected_value =
  Symb_execution.initialize ();
  Parser_main.verbose := true;
  let exp = Parser_main.exp_from_string p in
  let _ = Printf.printf "%s \n" (Pretty_print.string_of_exp_syntax exp.Parser_syntax.exp_stx) in
  let p_exp = exp_to_pulp exp in
  let _ = AllFunctions.iter (fun fid fwc -> Printf.printf "%s \n\n" (Pulp_Syntax_Print.string_of_func_block fwc)) p_exp in
  let result = Interpreter.run_with_initial_heap p_exp in
  assert_bool ("Incorrect Interpreter. Expected :" ^ (string_of_value expected_value) ^ " Actual: " ^ string_of_value (result.fs_return_value)) (value_eq expected_value ((result.fs_return_value))) 
  

let test_program1 () = 
  test_template "1" "P1" (VHValue (HVLiteral (Num 1.0)))
  
let test_program2 () = 
  test_template "var x = 2; x" "P2" (VHValue (HVLiteral (Num 2.0)))
  
let test_program3 () =
  test_template ("var x = {}; x.a = 1; x.b = 2; x.a + x.b") "P3" (VHValue (HVLiteral (Num 3.0)))
  
let test_program4 () =
  test_template ("var s = function (n) { 
   var t = function (m) { 
      return {x : n} 
    }; 
   var d = t(n); 
   return d 
}; 

var r = s(3).x; r") "P4" (VHValue (HVLiteral (Num 3.0)))
  
let suite = "Testing_Interpreter" >:::
  ["running program1" >:: test_program1;
   "running program2" >:: test_program2;
   "running_program3" >:: test_program3;
   "running_program4" >:: test_program4] 