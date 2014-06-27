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
  let exp = add_codenames exp in
  let _ = Printf.printf "Added codenames %s \n" (Pretty_print.string_of_exp true exp) in
  let all_functions = get_all_functions_with_env [] exp in
  let _ = List.iter (fun (fexp, fenv) -> 
  let fid = get_codename fexp in
  Printf.printf "Function id %s \n Function expression %s \n\n Function environment %s \n\n\n\n" 
     fid
     (Pretty_print.string_of_exp true fexp)
     (String.concat ";" (List.map Pulp_Syntax_Print.string_of_ctx_vars fenv)))
  all_functions in
  assert_bool "Incorrect Translation" true
  
let test_var_decl () = 
  test_template ("var x,y = 5; x.y")
  
let test_fun_def () =
  test_template ("var x = 1; var f = function (g) {var z = 1; x = 3; g = 4; var c = function (d) {}}; var g = function () {var x, a, b; }")
  
let test_call () =
  test_template ("f (4, true)")
  
let test_new () =
  test_template ("new f (1, \"a\")")
  
let test_caccess () =
  test_template ("x[y]")
  
let test_delete () =
  test_template ("delete x")
  
let test_bin_op_regular () =
  test_template ("y + z")
  
let test_bin_op_and () =
  test_template ("y && z")
  
let test_bin_op_or () =
  test_template ("y || z")
  
let test_popl12_example () =
  test_template ("var x = null, y = null, z = null; var f = function(w){x = v; v = 4; var v; y = v;}; v = 5; f(null); z = v;")


let suite = "Testing Translation" >:::
  ["translating access" >:: test_access;
   "translating assignment" >:: test_assign;
   "translating obj literal" >:: test_obj;
   "translating block" >:: test_block;
   "translating function environments" >:: test_fun_env;
   "translating var declarations" >:: test_var_decl;
   "translating function definition" >:: test_fun_def;
   "translating function call" >:: test_call;
   "translating new" >:: test_new;
   "translating computed access" >:: test_caccess;
   "translating delete" >:: test_delete;
   "translating regular binary op" >:: test_bin_op_regular;
   "translating and" >:: test_bin_op_and;
   "translating or" >:: test_bin_op_or;
  
   "translating popl12 example" >:: test_popl12_example] 