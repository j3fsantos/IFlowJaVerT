open OUnit
open Pulp_Procedure
open Control_Flow
open Pulp_Sym_Exec
open Pulp_Logic
open Pulp_Logic_Utils
open Pulp_Logic_Print

let apply_config () =  
  Config.apply_config ();
  CoreStar_Frontend_Pulp.initialize ()

let check_single_spec name f all_functions spec n =
  let path = "tests/dot/spec/" ^ name ^ f.func_name ^ (string_of_int n); in (* Fix if tests/dot/spec doesn't exist *)
  let cfg = fb_to_cfg f in
  let all_cfgs = AllFunctions.add f.func_name cfg AllFunctions.empty in
  print_cfg all_cfgs path;
      let sg, cmd_st_tbl = execute f cfg all_functions spec in
      let posts, throw_posts = get_posts f cfg sg cmd_st_tbl in
      
      Printf.printf "Printing state graph for %s" path; 
      State_Graph.print_state_graph sg cfg f.func_name path;
    
    (* For checking if end state implies given postcondition we need to subsitute #r with return/throw context var *)
   let spec_post = List.map (change_return f.func_ctx.return_var) spec.spec_post in     
   let spec_excep_post = List.map (change_return f.func_ctx.throw_var) spec.spec_excep_post in 
      
       assert_bool ("Symbolic Execution. Postcondition. 
         Expected :" ^ (String.concat "\n" (List.map string_of_formula spec_post)) ^ "Excep" ^  (String.concat "\n" (List.map string_of_formula spec_excep_post)) ^
       " Actual: " ^ (String.concat "\n" (List.map string_of_formula posts)) ^ "Excep" ^ (String.concat "\n Posts" (List.map string_of_formula throw_posts))) 
         ((List.for_all (fun post -> CoreStar_Frontend_Pulp.implies_or_list (simplify post) spec_post) posts)
         && (List.for_all (fun post -> CoreStar_Frontend_Pulp.implies_or_list (simplify post) spec_excep_post) throw_posts))