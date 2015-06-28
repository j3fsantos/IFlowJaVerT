open Pulp_Syntax
open Pulp_Procedure
open State_Graph
open Control_Flow
open Pulp_Logic
open Pulp_Logic_Rules
open Pulp_Logic_Utils

exception NotImplemented of string

type sym_exec_error =
  | CouldNotApplySpec

exception SymExecException of sym_exec_error

let execute_basic_stmt bs pre : formula =
  Printf.printf "Execute Basic Stmt \n" ;
  (* pre => pre_stmt' * F*)
  (* post_stmt' * F *)
  
  let cmd_pre, cmd_post = small_axiom_basic_stmt bs in
  
  let posts = CoreStar_Frontend_Pulp.apply_spec pre cmd_pre cmd_post in
  
  match posts with
    | None -> 
      begin 
        Printf.printf "Could Not Apply Spec";
        raise (SymExecException CouldNotApplySpec) 
      end
    | Some posts ->
      begin match posts with 
        | [post] -> 
          begin 
            Printf.printf "Postcondition %s \n" (Pulp_Logic_Print.string_of_formula post);
            post
          end
        | posts -> raise (NotImplemented "Multiple frames")
      end
      
let execute_call_stmt fs c current : formula list * formula list =
  (*let fb = AllFunctions.find c.call_name fs in
  let f_spec = c.func_spec in*)
  [], []
 

let rec execute_stmt f sg cfg fs snode_id cmd_st_tbl = 
 
  (* Hashtable cfg_node -> state_node list for termination *)
  let new_snode id state =
    let new_sn = StateG.mk_node sg (mk_sg_node id state) in
    Hashtbl.add cmd_st_tbl id new_sn;
    execute_stmt f sg cfg fs new_sn cmd_st_tbl in
    
  let new_snode_cond id state edge e =
    match edge with
      | Simp_Common.Edge_True -> new_snode id (Star (Eq (e, Le_Literal (Bool true)) :: [state]))
      | Simp_Common.Edge_False -> new_snode id (Star (Eq (e, Le_Literal (Bool false)) :: [state]))
      | _ -> raise (Invalid_argument "Expected true and false edges") in

  let new_snode_call id edge p_normal p_excep =
    match edge with
      | Simp_Common.Edge_Normal -> new_snode id p_normal
      | Simp_Common.Edge_Excep -> new_snode id p_excep
      | _ -> raise (Invalid_argument "Expected normal and exceptional edges") in
    
  let get_single_succ id =
    let succs = CFG.succ cfg id in
      begin match succs with
        | [succ] -> succ
        | _ -> raise (Invalid_argument "Expected single successor")
      end in
      
  let get_two_succs id =
    let succs = CFG.succ cfg id in
      begin match succs with
        | [succ1; succ2] -> succ1, succ2
        | _ -> raise (Invalid_argument "Expected two successor")
      end in
 
  let snode = StateG.get_node_data sg snode_id in
  let stmt = CFG.get_node_data cfg snode.sgn_id in
  
  Printf.printf "Execute Stmt %s \n" (Pulp_Syntax_Print.string_of_statement stmt);
  
  match stmt with
    | Label l -> 
      if l = f.func_ctx.label_return or l = f.func_ctx.label_throw 
      then () 
      else new_snode (get_single_succ snode.sgn_id) snode.sgn_state
      
    | Goto l -> new_snode (get_single_succ snode.sgn_id) snode.sgn_state
    
    | GuardedGoto (e, l1, l2) -> 
      let succ1, succ2 = get_two_succs snode.sgn_id in
      let edge1 = CFG.get_edge_data cfg snode.sgn_id succ1 in
      let edge2 = CFG.get_edge_data cfg snode.sgn_id succ2 in
      new_snode_cond succ1 snode.sgn_state edge1 (expr_to_logical_expr e);
      new_snode_cond succ2 snode.sgn_state edge2 (expr_to_logical_expr e)
    
    | Basic (Assignment {assign_right = (Call c)})      
    | Basic (Assignment {assign_right = (Eval c)}) 
    | Basic (Assignment {assign_right = (BuiltinCall c)}) -> 
      let succ1, succ2 = get_two_succs snode.sgn_id in
      let edge1 = CFG.get_edge_data cfg snode.sgn_id succ1 in
      let edge2 = CFG.get_edge_data cfg snode.sgn_id succ2 in
      
      let post_normal, post_excep = execute_call_stmt fs c snode.sgn_state in
      List.iter2 (new_snode_call succ1 edge1) post_normal post_excep;
      List.iter2 (new_snode_call succ2 edge2) post_normal post_excep
      
    | Basic bs -> 
      let post = execute_basic_stmt bs snode.sgn_state in
      new_snode (get_single_succ snode.sgn_id) post 
    | Sugar s -> raise (Invalid_argument "Symbolic execution does not work on syntactic sugar")


(* I have assumptions about return labels. Do I want to add "exit" labels to the cfg interface *)
let get_posts fb cfg sg cmd_st_tbl =
  let return_label = fb.func_ctx.label_return in
  let label_map = get_all_labels cfg in (* Something not right in the interface *)
  let return_label_node = Hashtbl.find label_map return_label in
  let posts_nodes = Hashtbl.find_all cmd_st_tbl return_label_node in
  let posts = List.map (fun id -> let snode = StateG.get_node_data sg id in snode.sgn_state) posts_nodes in
  posts
  
(* returns a state graph *)
(*         and a map cfg_node -> state_node list*)
let execute f cfg fs spec =
  let label_map = get_all_labels cfg in (* Something not right in the interface *)
  
  let start = Hashtbl.find label_map Simp_Common.entry in
  
  (* cfg_node -> state_node list *)
  let cmd_st_tbl = Hashtbl.create 100 in
  
  (* state graph *)
  let sg = StateG.mk_graph () in
  let first = StateG.mk_node sg (mk_sg_node start spec.spec_pre) in
  
  Hashtbl.add cmd_st_tbl start first;
  
  execute_stmt f sg cfg fs first cmd_st_tbl; 
  sg, cmd_st_tbl
  
let execute_check_post f cfg fs spec =
  let sg, cmd_st_tbl = execute f cfg fs spec in
  let posts = get_posts f cfg sg cmd_st_tbl in
  List.for_all (fun post -> CoreStar_Frontend_Pulp.implies_or_list (simplify post) spec.spec_post) posts
  
let execute_all (f : function_block) (fs : function_block AllFunctions.t) = 
  let cfg = fb_to_cfg f in
  List.iter (fun spec -> ignore (execute f cfg fs spec)) f.func_spec