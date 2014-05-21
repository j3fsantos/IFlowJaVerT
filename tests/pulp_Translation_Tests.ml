open OUnit
open Pulp_Syntax
open Pulp_Translate

let test_template p =
  Symb_execution.initialize ();
  Parser_main.verbose := true;
  let exp = Parser_main.exp_from_string p in
  let _ = Printf.printf "%s \n" (Pretty_print.string_of_exp_syntax exp.Parser_syntax.exp_stx) in
  let p_exp = exp_to_pulp exp in
  let _ = List.iter (fun fb -> Printf.printf "%s \n\n" (Pulp_Syntax_Print.string_of_func_block fb)) p_exp in
  assert_bool "Incorrect Translation" true
  

let test_access () = 
  test_template ("x.y")
  
let test_assign () =
  test_template ("x = y")
  
let test_obj () =
  test_template ("obj = {x : 1, y : null, z : false}") 
  
let test_block () =
  test_template ("x = y; y = z")


let suite = "Testing Translation" >:::
  ["translating access" >:: test_access;
   "translating assignment" >:: test_assign;
   "translating obj literal" >:: test_obj;
   "translating block" >:: test_block] 