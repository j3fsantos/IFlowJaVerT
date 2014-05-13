open OUnit
open Pulp_Syntax
open Pulp_Translate

let test_access () = 
  Symb_execution.initialize ();
  Parser_main.verbose := true;
  let exp = Parser_main.exp_from_string "x.y" in
  let _ = Printf.printf "%s \n" (Pretty_print.string_of_exp_syntax exp.Parser_syntax.exp_stx) in
  let p_exp = exp_to_pulp exp in
  let _ = List.iter (fun fb -> Printf.printf "%s \n\n" (Pulp_Syntax_Print.string_of_func_block fb)) p_exp in
  assert_bool "Incorrect Translation" false

let suite = "Testing Translation" >:::
  ["translating access" >:: test_access]