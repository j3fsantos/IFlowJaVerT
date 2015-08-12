open Pulp_Syntax
open Pulp_Procedure
open State_Graph
open Control_Flow
open Pulp_Logic
open Pulp_Logic_Rules
open Pulp_Logic_Utils

exception NotImplemented of string

exception SymExecException of string

let execute_basic_stmt bs pre : formula =
  Printf.printf "Execute Basic Stmt \n" ;
  (* pre => pre_stmt' * F*)
  (* post_stmt' * F *)
  
  let cmd_pre, cmd_post = small_axiom_basic_stmt bs in
  Printf.printf "Got spec for Basic Stmt \n" ;
  
  let posts = CoreStar_Frontend_Pulp.apply_spec pre cmd_pre cmd_post in
  
  Printf.printf "Got Postcondition \n" ;

  
  match posts with
    | None -> 
      begin 
        Printf.printf "Could Not Apply Spec";
        raise (SymExecException "CouldNotApplySpec") 
      end
    | Some posts ->
      begin match posts with 
        | [] -> raise (NotImplemented "Frame Not Found")
        | [post] -> 
          begin 
            Printf.printf "Postcondition %s \n" (Pulp_Logic_Print.string_of_formula post);
            post
          end
        | posts -> 
          List.iter (fun post -> Printf.printf "Postcondition %s \n" (Pulp_Logic_Print.string_of_formula post)) posts;
          raise (NotImplemented "Multiple frames")
      end
      
let execute_call_stmt x fs c current : formula list * formula list =
  let get_posts fb f_spec excep = 
    let posts = Utils.flat_map (fun spec -> 
    let spec_post = if excep then spec.spec_excep_post else spec.spec_post in
    let call_args = [c.call_this; c.call_scope] @ c.call_args in

    Printf.printf "Map2 lenght1 %d lenght2 %d \n" (List.length fb.func_params) (List.length call_args);
    
    let used_args = List.mapi (fun i p ->
      if i < List.length call_args then expr_to_logical_expr (List.nth call_args i)
      else Le_Literal Undefined
      ) fb.func_params in
    
    (* Make a varmap formal_param -> argument *)
    let varmap = List.fold_left2 (fun varmap param arg ->
      ProgramVarMap.add param arg varmap
    ) ProgramVarMap.empty fb.func_params used_args in
    
    let posts = List.map (fun post ->
      (* Substituting formal params in the spec *)
      let pre = subs_pvars varmap spec.spec_pre in
      let post = subs_pvars varmap post in
      let (current, pre, post) = match CoreStar_Frontend_Pulp.universal_to_substitutable ([current; pre; post]) with
        | [a; b; c] -> (a, b, c)
        | _ -> raise Utils.CannotHappen in
      CoreStar_Frontend_Pulp.apply_spec current pre post
    ) spec_post in
    
   let posts = List.flatten (List.fold_left (fun result post -> match post with
      | None -> result
      | Some post -> post :: result) [] posts) in

    (* substitute #r = E to x = E *)
    let posts = List.map (change_return x) posts in posts
      
    ) f_spec in
    match posts with
      | [] -> [false_f]
      | posts -> posts in
    

  
  let fid = CoreStar_Frontend_Pulp.get_function_id_from_expression current (expr_to_logical_expr c.call_name) in
  let fb = AllFunctions.find fid fs in
  let f_spec = fb.func_spec in
  let posts_normal = get_posts fb f_spec false in
  let posts_excep = get_posts fb f_spec true in
  posts_normal, posts_excep
  
let execute_proto_field current e1 e2 =
  let ls = Le_Var (fresh_e ()) in
  let l = Le_Var (fresh_e ()) in
  let v = Le_Var (fresh_e ()) in
  let pi = Pi (mk_pi_pred ls e1 e2 l v) in
  let posts = CoreStar_Frontend_Pulp.apply_spec current pi (Star [pi; REq v]) in
  let posts = match posts with
    | None -> raise (SymExecException "CouldNotApplySpec")
    | Some posts -> posts in
  let values = List.map get_return posts in 
  let values = List.fold_left (fun result v -> match v with 
    | None -> result
    | Some v -> v :: result) [] values in
  match values with
    | [] -> raise (SymExecException "CouldNotApplySpec")
    | _ -> values
 
let rec execute_stmt f sg cfg fs snode_id cmd_st_tbl = 
  let contradiction id =
    let new_sn = StateG.mk_node sg (mk_sg_node id false_f) in
    Hashtbl.add cmd_st_tbl id new_sn;
    StateG.mk_edge sg snode_id new_sn () in
         
 
  (* Hashtable cfg_node -> state_node list for termination *)
  let new_snode id state =
    let new_sn = StateG.mk_node sg (mk_sg_node id state) in
    Hashtbl.add cmd_st_tbl id new_sn;
    StateG.mk_edge sg snode_id new_sn ();
    execute_stmt f sg cfg fs new_sn cmd_st_tbl in
    
  let new_snode_cond id state edge e =
    
    let exprs_true = get_proof_cases_eq_true e in
    let exprs_false = get_proof_cases_eq_false e in
    
    Printf.printf "Guarded Goto"; 
    match edge with
      | Simp_Common.Edge_True -> 
        Printf.printf "Guarded Goto true"; 
        List.iter (fun expr_true ->     
          let state_true = combine expr_true state in
          Format.pp_print_flush(Format.std_formatter)();
          Printf.printf "Guarded Goto true state %s" (Pulp_Logic_Print.string_of_formula expr_true); 
          Printf.printf "Guarded Goto true state %s" (Pulp_Logic_Print.string_of_formula state_true); 
	        if CoreStar_Frontend_Pulp.inconsistent state_true then
            begin Printf.printf "Contradiction found ";
	          contradiction id end
	        else begin Printf.printf "Contradiction not found "; new_snode id state_true end        
        ) exprs_true
        
      | Simp_Common.Edge_False ->  
         List.iter (fun expr_false ->  
          let state_false = combine expr_false state in
          Format.pp_print_flush(Format.std_formatter)();
          Printf.printf "Guarded Goto false state %s" (Pulp_Logic_Print.string_of_formula expr_false);  
          Printf.printf "Guarded Goto true state %s" (Pulp_Logic_Print.string_of_formula state_false);    
          if CoreStar_Frontend_Pulp.inconsistent state_false then
          begin Printf.printf "Contradiction found ";
              contradiction id end
            else begin Printf.printf "Contradiction not found "; new_snode id state_false end
        ) exprs_false        
        
      | _ -> raise (Invalid_argument "Expected true and false edges") in

  let new_snode_call id edge p_normal p_excep =
    match edge with
      | Simp_Common.Edge_Normal -> if CoreStar_Frontend_Pulp.inconsistent p_normal then contradiction id else new_snode id p_normal
      | Simp_Common.Edge_Excep -> if CoreStar_Frontend_Pulp.inconsistent p_excep then contradiction id else new_snode id p_excep
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
  
  Printf.printf "********Execute Stmt %s *********\n" (Pulp_Syntax_Print.string_of_statement stmt);
  
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
    
    | Basic (Assignment {assign_left = x; assign_right = (Call c)})      
    | Basic (Assignment {assign_left = x; assign_right = (Eval c)}) 
    | Basic (Assignment {assign_left = x; assign_right = (BuiltinCall c)}) -> 
      
      let succ1, succ2 = get_two_succs snode.sgn_id in
      let edge1 = CFG.get_edge_data cfg snode.sgn_id succ1 in
      let edge2 = CFG.get_edge_data cfg snode.sgn_id succ2 in
      
      let post_normal, post_excep = execute_call_stmt x fs c snode.sgn_state in
      List.iter2 (new_snode_call succ1 edge1) post_normal post_excep;
      List.iter2 (new_snode_call succ2 edge2) post_normal post_excep
      
    | Basic (Assignment {assign_left = x; assign_right = (ProtoF (e1, e2))}) -> 
      Printf.printf "Execute protoField \n";
      let id = get_single_succ snode.sgn_id in
      let values = execute_proto_field snode.sgn_state (expr_to_logical_expr e1) (expr_to_logical_expr e2) in
      Printf.printf "GotValues \n";
      List.iter (fun value ->
        let post = combine snode.sgn_state (Eq (Le_PVar x, value)) in
        new_snode id post
      ) values
      
    | Basic (Assignment {assign_right = (ProtoO (e1, e2))}) -> raise (NotImplemented "ProtoObj")
     
    | Basic bs -> 
        let id = get_single_succ snode.sgn_id in
        begin try
          let post = execute_basic_stmt bs snode.sgn_state in
          new_snode id post 
        with CoreStar_Frontend_Pulp.ContradictionFound ->
          contradiction id
        end
        
    | Sugar s -> raise (Invalid_argument "Symbolic execution does not work on syntactic sugar")


(* I have assumptions about return labels. Do I want to add "exit" labels to the cfg interface *)
let get_posts fb cfg sg cmd_st_tbl =
  let return_label = fb.func_ctx.label_return in
  let label_map = get_all_labels cfg in (* Something not right in the interface *)
  let return_label_node = Hashtbl.find label_map return_label in
  let posts_nodes = Hashtbl.find_all cmd_st_tbl return_label_node in
  let posts = List.map (fun id -> let snode = StateG.get_node_data sg id in snode.sgn_state) posts_nodes in
  
  let throw_label = fb.func_ctx.label_throw in
  let throw_label_node = Hashtbl.find label_map throw_label in
  let posts_nodes_throw = Hashtbl.find_all cmd_st_tbl throw_label_node in
  let posts_throw = List.map (fun id -> let snode = StateG.get_node_data sg id in snode.sgn_state) posts_nodes_throw in
  posts, posts_throw
  
(* returns a state graph *)
(*         and a map cfg_node -> state_node list*)
let execute f cfg fs spec =
  let label_map = get_all_labels cfg in (* Something not right in the interface *)
  
  let start = Hashtbl.find label_map Simp_Common.entry in
  
  (* cfg_node -> state_node list *)
  let cmd_st_tbl = Hashtbl.create 100 in
  
  (* state graph *)
  let sg = StateG.mk_graph () in
  let params_not_none = Star (List.map (fun p -> NEq (Le_PVar p, Le_None)) f.func_params) in 
  let pre = combine spec.spec_pre params_not_none in
  let first = StateG.mk_node sg (mk_sg_node start pre) in
  
  Hashtbl.add cmd_st_tbl start first;
  
  execute_stmt f sg cfg fs first cmd_st_tbl; 
  sg, cmd_st_tbl
  
let execute_check_post f cfg fs spec =
  let sg, cmd_st_tbl = execute f cfg fs spec in
  let posts, throw_posts = get_posts f cfg sg cmd_st_tbl in
  List.for_all (fun post -> CoreStar_Frontend_Pulp.implies_or_list (simplify post) spec.spec_post) posts
  
let execute_all (f : function_block) (fs : function_block AllFunctions.t) = 
  let cfg = fb_to_cfg f in
  List.iter (fun spec -> ignore (execute f cfg fs spec)) f.func_spec