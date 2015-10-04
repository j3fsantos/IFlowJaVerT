open Basic_Blocks
open Utils
open Pulp_Syntax
open Simp_Common
open Pulp_Procedure
open Control_Flow
open Pulp_Translate

let unfold_spec_func left sf annot =
  let ctx =  {
     env_vars = [];  (*unused*)
     return_var = left;
     throw_var = left;
     label_entry = "entry." ^ fresh_r (); 
     label_return = "return." ^ fresh_r (); 
     label_throw = "throw." ^ fresh_r (); 
     label_continue = [];  (*unused*)
     label_break = [];  (*unused*)
     stmt_return_var = fresh_r();  (*unused*)
  } in
  let throw_var = ctx.throw_var in
  let label_throw = ctx.label_throw in
  let stmts = to_ivl_goto (unfold_spec_function sf left throw_var label_throw) in
  let stmts = stmts @ [Goto ctx.label_return; Label ctx.label_return; Label ctx.label_throw] in
  Printf.printf "Simplified spec function %s : %s" (Pulp_Syntax_Print.string_of_spec_function sf) (Pulp_Syntax_Print.string_of_statement_list stmts);
  make_function_block "" stmts [] ctx
  

let transform_spec_funcs cfg sf_annot n_normal n_excep = 
  match sf_annot.as_stmt with
    | Sugar (SpecFunction (left, sf, excep_label)) ->       
      let fb = unfold_spec_func left sf sf_annot.as_annot in
      
      let fb_cfg = fb_to_cfg fb in
      let fb_cfg_bb = transform_to_basic_blocks_from_cfg fb_cfg fb.func_ctx in
      CFG_BB.inject_graph cfg fb_cfg_bb;
      print_cfg_bb_single fb_cfg_bb "test";
      
      let all_labels = get_block_labels cfg in
      let return_node = Hashtbl.find all_labels fb.func_ctx.label_return in
      let throw_node = Hashtbl.find all_labels fb.func_ctx.label_throw in
      
      (* connect inject subgraph *)
      connect_blocks cfg return_node n_normal;
      connect_blocks cfg throw_node n_excep;
      
      Hashtbl.find all_labels fb.func_ctx.label_entry
    | _ -> raise (Invalid_argument "Expected SpecFunction")

(* Assumptions -- spec functions last commands in the block*)
(* and that they have two outgoing edges *)
let simplify_spec_functions cfg =
  let nodes = CFG_BB.nodes cfg in
  List.iter (fun n ->
    let stmts = CFG_BB.get_node_data cfg n in
    
    let rev_stmts = List.rev stmts in
    match rev_stmts with
      | [] -> raise (Invalid_argument "Statement list in basic block should not be empty")
      | ({as_stmt = Sugar (SpecFunction _)} as s1) :: tail ->
        begin
          let succs = CFG_BB.succ cfg n in
          let n_normal, n_excep = match succs with
            | [succ1; succ2] -> 
              begin
                match CFG_BB.get_edge_data cfg n succ1, CFG_BB.get_edge_data cfg n succ2 with
                  | Edge_Normal, Edge_Excep -> succ1, succ2
                  | Edge_Excep, Edge_Normal -> succ2, succ1
                  | _ ->  raise (Invalid_argument "Spec Functions should have one normal and one exceptional successor")
              end
            | _ -> raise (Invalid_argument "Spec Functions should have two successors") in
          (* Entry node of the unfolded spec func control flow subgraph *)
          
          let n_normal_stmts = CFG_BB.get_node_data cfg n_normal in
          CFG_BB.set_node_data cfg n_normal ((as_annot_stmt(Label (fresh_r()))) :: n_normal_stmts);
          
          CFG_BB.rm_edge cfg n n_normal;
          CFG_BB.rm_edge cfg n n_excep;
          
          let entry_n = transform_spec_funcs cfg s1 n_normal n_excep in 
          let entry_label = get_block_label cfg entry_n in
          
          let updated_stmts = List.rev ((as_annot_stmt(Goto entry_label)) :: tail) in
          CFG_BB.set_node_data cfg n updated_stmts;
          
          CFG_BB.mk_edge cfg n entry_n Edge_Normal
          
        end
      | _ -> ()
    
  ) nodes