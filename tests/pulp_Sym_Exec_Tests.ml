open OUnit
open Pulp_Logic
open Pulp_Syntax
open Pulp_Sym_Exec
open Pulp_Procedure
open Control_Flow
open Pulp_Logic_Print
open Pulp_Logic_Utils

let test_program1 () = 
  Printf.printf "Test Program 1\n" ;
  let ctx = create_ctx [] in
  let ivl_program = [
      Basic Skip;       
      Goto ctx.label_return; 
      Label ctx.label_return
  ] in
  let spec = mk_spec empty_f [empty_f] in
  let f = make_function_block_with_spec "fid1" ivl_program [] ctx [spec] in
  let all_functions = AllFunctions.add "fid1" f AllFunctions.empty in
  let cfg = fb_to_cfg f in
  let all_cfgs = AllFunctions.add "fid1" cfg AllFunctions.empty in
  print_cfg all_cfgs ("/Users/daiva/Documents/workspace/JS_Symbolic_Debugger/JS_Symbolic_Debugger/tests/dot/fid1");
  
  let sg, cmd_st_tbl = execute f cfg all_functions spec in
  let posts = get_posts f cfg all_functions spec sg cmd_st_tbl in
  
  match posts with
    | [post] -> 
      assert_bool ("Symbolic Execution. Postcondition. Expected :" ^ (string_of_formula empty_f) ^ " Actual: " ^ (string_of_formula post)) (simplify post=simplify (Star[empty_f])) 
    | _ -> assert_failure "Must exists only one postcondition"
  
  
let suite = "Testing_Sym_Exec" >:::
  ["running program1" >:: test_program1]