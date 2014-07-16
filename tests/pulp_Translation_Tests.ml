open OUnit
open Pulp_Syntax
open Pulp_Translate
open Pulp_Syntax_Utils

let test_template p name =
  Symb_execution.initialize ();
  Parser_main.verbose := true;
  let exp = Parser_main.exp_from_string p in
  let _ = Printf.printf "%s \n" (Pretty_print.string_of_exp_syntax exp.Parser_syntax.exp_stx) in
  let p_exp = exp_to_pulp exp in
  let _ = AllFunctions.iter (fun fid fwc -> Printf.printf "%s \n\n" (Pulp_Syntax_Print.string_of_func_block fwc)) p_exp in
  (* TODO fix path *)
  let _ = Cfg.mk_cfg p_exp ("/Users/daiva/Documents/workspace/JS_Symbolic_Debugger/JS_Symbolic_Debugger/tests/dot/"^name) in
  assert_bool "Incorrect Translation" true
  

let test_access () = 
  test_template ("x.y") "access"
  
let test_assign () =
  test_template ("x = y") "assign"
  
let test_obj () =
  test_template ("obj = {x : 1, y : null, z : false}") "obj"
  
let test_block () =
  test_template ("x = y; y = z") "block"
  
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
  test_template ("var x,y = 5; x.y") "vardecl"
  
let test_fun_def () =
  test_template ("var x = 1; var f = function (g) {var z = 1; x = 3; g = 4; var c = function (d) {}}; var g = function () {var x, a, b; }") "fundef"
  
let test_call () =
  test_template ("f (4, true)") "call"
  
let test_new () =
  test_template ("new f (1, \"a\")") "new"
  
let test_caccess () =
  test_template ("x[y]") "access"
  
let test_delete () =
  test_template ("delete x") "delete"
  
let test_bin_op_regular () =
  test_template ("y + z") "binopreg"
  
let test_bin_op_and () =
  test_template ("y && z") "binopand"
  
let test_bin_op_or () =
  test_template ("y || z") "binopor"
  
let test_if () =
  test_template ("if (x == true) {x = 1} else {x = 2; y = 2}") "if"
  
let test_if_no_else () =
  test_template ("if (x == true) {x = 1}") "ifnoelse"
  
let test_while () =
  test_template ("while (x == 5) {x = x - 1; z = z + 1}") "while"
  
let test_return () =
  test_template ("function () {return}") "return"
  
let test_return_exp () =
  test_template ("function () {var x; return x}") "returnexp"
  
let test_same_name_param_var () =
  test_template ("function (b) {var b}") "samevar"
  
let test_popl12_example () =
  test_template ("var x = null, y = null, z = null; var f = function(w){x = v; v = 4; var v; y = v;}; v = 5; f(null); z = v;") "popl12"
  
let test_small_example () =
  test_template ("var x = {}; var f = function(field, value){x[field] = value}; f(\"a\", 1);") "small example"
  
let test_smaller_example () =
  test_template ("var x = {}; x.a = 1; x.b = 2") "smaller example"
  
let test_example () =
  test_template ("var x = {a : 1}; var y = x.a") "example"


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
   "translating if" >:: test_if;
   "translating if without else" >:: test_if_no_else;
   "translating while" >:: test_while;
   "testing return" >:: test_return;
   "testing return with expression" >:: test_return_exp;
   "testing function that has same name for one of the parameters and variable declaration" >:: test_same_name_param_var;
   "translating popl12 example" >:: test_popl12_example;
   "translating small explample" >:: test_small_example;
   "translating smaller explample" >:: test_smaller_example;
   "test_example" >:: test_example] 