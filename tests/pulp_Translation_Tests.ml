open OUnit
open Pulp_Syntax
open Pulp_Translate
open Pulp_Syntax_Utils

let test_template p =
  Symb_execution.initialize ();
  Parser_main.verbose := true;
  let exp = Parser_main.exp_from_string p in
  let _ = Printf.printf "%s \n" (Pretty_print.string_of_exp_syntax exp.Parser_syntax.exp_stx) in
  let p_exp = exp_to_pulp exp in
  let _ = AllFunctions.iter (fun fid fwc -> Printf.printf "%s \n\n" (Pulp_Syntax_Print.string_of_fun_with_ctx fwc)) p_exp in
  assert_bool "Incorrect Translation" true
  

let test_access () = 
  test_template ("x.y")
  
let test_assign () =
  test_template ("x = y")
  
let test_obj () =
  test_template ("obj = {x : 1, y : null, z : false}") 
  
let test_block () =
  test_template ("x = y; y = z")
  
let test_fun_env () =
  Symb_execution.initialize ();
  Parser_main.verbose := true;
  let exp = Parser_main.exp_from_string "var x = 1; var f = function (g) {var z = 1; var c = function (d) {}}; var g = function z () {var x, a, b; }" in
  let _ = Printf.printf "%s \n" (Pretty_print.string_of_exp_syntax exp.Parser_syntax.exp_stx) in
  let all_functions = get_all_functions_with_env [] exp in
  let _ = List.iter (fun (fid, fexp, fenv) -> Printf.printf "Function id %s \n Function expression %s \n\n Function environment %s \n\n\n\n" 
     fid
     (Pretty_print.string_of_exp_syntax fexp.Parser_syntax.exp_stx)
     (String.concat ";" (List.map Pulp_Syntax_Print.string_of_ctx_vars fenv)))
  all_functions in
  assert_bool "Incorrect Translation" true
  
let test_var_decl () = 
  test_template ("var x,y = 5; x.y")


let suite = "Testing Translation" >:::
  ["translating access" >:: test_access;
   "translating assignment" >:: test_assign;
   "translating obj literal" >:: test_obj;
   "translating block" >:: test_block;
   "testing function environments" >:: test_fun_env;
   "testing var declarations" >:: test_var_decl] 