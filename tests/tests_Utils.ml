(* ./tests/tests_Utils.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open OUnit
open Pulp_Procedure
open Control_Flow
open Pulp_Sym_Exec
open Pulp_Logic
open Pulp_Logic_Utils
open Pulp_Logic_Print
open Pulp_Translate

let apply_config () =  
  Config.apply_config ();
  CoreStar_Frontend_Pulp.initialize ()

let check_single_spec name f all_functions spec n path =
  let path = path ^ name ^ f.func_name ^ (string_of_int n); in (* Fix if tests/dot/spec doesn't exist *)
  let cfg = fb_to_cfg f in
  let all_cfgs = AllFunctions.add f.func_name cfg AllFunctions.empty in
  print_cfg all_cfgs path;
  
  let print_state_graph sg =
    Printf.printf "Printing state graph for %s" path; 
    State_Graph.print_state_graph sg cfg f.func_name path in
  
  let sg, cmd_st_tbl = 
    try 
      execute f cfg all_functions (Spec_Fun_Specs.get_env_spec()) spec 
    with SymExecExcepWithGraph (msg, offset, sg) -> 
      print_state_graph sg;
      raise (SymExecException (msg, offset)) in
      
   print_state_graph sg;   
       
  (* For checking if end state implies given postcondition we need to subsitute #r with return/throw context var *)
  let posts, throw_posts = get_posts f cfg sg cmd_st_tbl in
  let spec_post = List.map (change_return f.func_ctx.return_var) spec.spec_post in     
  let spec_excep_post = List.map (change_return f.func_ctx.throw_var) spec.spec_excep_post in     
    assert_bool ("Symbolic Execution. Postcondition. 
      Expected :" ^ (String.concat "\n" (List.map string_of_formula spec_post)) ^ "Excep" ^  (String.concat "\n" (List.map string_of_formula spec_excep_post)) ^
      " Actual: " ^ (String.concat "\n" (List.map string_of_formula posts)) ^ "Excep" ^ (String.concat "\n Posts" (List.map string_of_formula throw_posts))) 
      ((List.for_all (fun post -> CoreStar_Frontend_Pulp.implies_or_list (simplify post) spec_post) posts)
      && (List.for_all (fun post -> CoreStar_Frontend_Pulp.implies_or_list (simplify post) spec_excep_post) throw_posts))
        
let get_pexp js_program =
  apply_config ();
  let exp = Parser_main.exp_from_string js_program in
  let p_exp, p_env = exp_to_pulp IVL_goto_with_get_value exp "main" [] in
  let _ = AllFunctions.iter (fun fid fwc -> Printf.printf "%s \n\n" (Pulp_Syntax_Print.string_of_func_block fwc)) p_exp in
  let p_exp = Simp_Main.simplify p_exp Simp_Common.Simp_Specs in
  p_exp, p_env