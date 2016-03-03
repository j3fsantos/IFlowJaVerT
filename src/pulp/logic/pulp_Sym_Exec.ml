(* ./src/pulp/logic/pulp_Sym_Exec.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open Pulp_Syntax
open Pulp_Procedure
open State_Graph
open Control_Flow
open Pulp_Logic
open Pulp_Logic_Rules
open Pulp_Logic_Utils

exception NotImplemented of string

exception SymExecException of string * int option
exception SymExecExcepWithGraph of string * int option * StateG.graph

let execute_basic_stmt bs data pre : formula =
  Printf.printf "Execute Basic Stmt \n" ;
  (*Printf.printf "Precondition %s \n" (Pulp_Logic_Print.string_of_formula pre);*)
  (* pre => pre_stmt' * F*)
  (* post_stmt' * F *)
  
  let cmd_pre, cmd_post = small_axiom_basic_stmt bs in
  
  let posts = CoreStar_Frontend_Pulp.apply_spec pre cmd_pre cmd_post in  
  
  match posts with
    | None -> raise (SymExecException ("Could not apply small axiom for the basic statement" 
      ^ (Pulp_Syntax_Print.string_of_basic_statement bs), data.src_offset)) 
    | Some posts ->
      begin match posts with 
        | [] -> 
          raise (SymExecException ("Contradiction found when executing basic statement" ^
          (Pulp_Syntax_Print.string_of_basic_statement bs), data.src_offset))
        | [post] -> 
          begin 
            (*Printf.printf "Postcondition %s \n" (Pulp_Logic_Print.string_of_formula post);*)
            post
          end
        | posts -> 
          List.iter (fun post -> Printf.printf "Postcondition %s \n" (Pulp_Logic_Print.string_of_formula post)) posts;
          raise (NotImplemented "Multiple frames")
      end
      

let execute_call_stmt varmap x fid fb data fs current : formula list * formula list =
  let get_posts fb f_spec excep = 
    let posts = Utils.flat_map (fun spec -> 
    let spec_post = if excep then spec.spec_excep_post else spec.spec_post in
    
    let posts = List.map (fun post ->
      (* Substituting formal params in the spec *)
      let pre = subs_pvars varmap spec.spec_pre in
      let post = subs_pvars varmap post in
      let (current, pre, post) = match CoreStar_Frontend_Pulp.universal_to_substitutable ([current; pre; post]) with
        | [a; b; c] -> (a, b, c)
        | _ -> raise Utils.CannotHappen in
      try
         CoreStar_Frontend_Pulp.apply_spec current pre post
       with CoreStar_Frontend_Pulp.ContradictionFound -> raise (SymExecException ("Contradiction found in function call", data.src_offset))
    ) spec_post in
    
   let posts = List.flatten (List.fold_left (fun result post -> match post with
      | None -> result
      | Some post -> post :: result) [] posts) in

    (* substitute #r = E to x = E *)
    let posts = List.map (change_return x) posts in 
    let posts = List.map CoreStar_Frontend_Pulp.elim_vars_in_formula posts in 
    (*List.iter (fun post -> Printf.printf "Postcondition %s \n" (Pulp_Logic_Print.string_of_formula post)) posts;*)
    posts
      
    ) f_spec in
    match posts with
      | [] -> []
      | posts -> posts in
  
  let f_spec = fb.func_spec in
  let posts_normal = get_posts fb f_spec false in
  let posts_excep = get_posts fb f_spec true in
  let posts_normal, posts_excep =
    match posts_normal, posts_excep with
      | [], [] -> raise (SymExecException (("Cannot apply any of the spec for procedure " ^ fb.func_name), data.src_offset))
      | [], e -> [false_f], e
      | n, [] -> n, [false_f]
      | n, e -> n, e in
  posts_normal, posts_excep
      
let execute_normal_call_stmt c data is_builtin x fs current : formula list * formula list =
   let fid = CoreStar_Frontend_Pulp.get_function_id_from_expression current (expr_to_logical_expr c.call_name) in
   let fb = AllFunctions.find fid fs in
   let call_args = [c.call_this; c.call_scope] @ c.call_args in

    Printf.printf "Map2 lenght1 %d lenght2 %d \n" (List.length fb.func_params) (List.length call_args);
    
    let used_args = List.mapi (fun i p ->
      if i < List.length call_args then expr_to_logical_expr (List.nth call_args i)
      else if is_builtin then Le_Literal Empty else Le_Literal Undefined
      ) fb.func_params in
    
    (* Make a varmap formal_param -> argument *)
    let varmap = List.fold_left2 (fun varmap param arg ->
      ProgramVarMap.add param arg varmap
    ) ProgramVarMap.empty fb.func_params used_args in
    
  execute_call_stmt varmap x fid fb data fs current
  
let observe_state current v pre data =
  let posts = 
    (*try*) CoreStar_Frontend_Pulp.apply_spec current pre (combine pre (REq v))
    (*with CoreStar_Frontend_Pulp.ContradictionFound -> raise (SymExecException "Contradiction found in basic stmt")*) in
  let posts = match posts with
    | None -> raise (SymExecException ("Observing State No Postcondition Found", data.src_offset))
    | Some posts -> posts in
  let values = List.map get_return posts in 
  let values = List.fold_left (fun result v -> match v with 
    | None -> result
    | Some v -> v :: result) [] values in
  match values with
    | [] -> raise (SymExecException ("Observing State No Return Found", data.src_offset))
    | _ -> values

(* returns the list of normal post conditions and exceptional post conditions *)    
let execute_spec_func_call_stmt sf data x fs current : formula list * formula list =
    let excep_post () = 
      let lerror = Le_Var (fresh_e()) in
       combine current (Star [
                         Eq (Le_PVar x, lerror);
                         proto_heaplet_f lerror (Le_Literal (LLoc Lrep));
                         class_heaplet_f lerror "Error"]) in
                        
                        
    let mem_ref_cases le1 = 
      (* member reference not empty *)  
      let values = try 
        let v = Le_Var (fresh_e()) in
        observe_state current v (Spec_Fun_Specs.get_value_mref_not_empty_pre le1 v) data
      with SymExecException _ -> [] in
                        
      begin match values with
        | value :: rest ->
          List.map (fun value ->
            combine current (Eq (Le_PVar x, value))
          ) values, [false_f]  
                                          
       | [] -> 
         (* member reference object empty *)

         if (CoreStar_Frontend_Pulp.implies current (Spec_Fun_Specs.get_value_mref_empty_pre le1)) then 
           [combine current (Eq (Le_PVar x, Le_Literal Undefined))], [false_f] 
         else raise (SymExecException ("Not Implemented Branching in GetValue", data.src_offset))
      end in     
      
    let var_ref_cases le1 continue = 
      let values = try 
        let v = Le_Var (fresh_e()) in
        observe_state current v (Spec_Fun_Specs.get_value_vref_obj_pre le1 v) data
        with SymExecException _ -> [] in
                     
      begin match values with
        | value :: rest ->                       
          (* variable reference not lg *)
          List.map (fun value ->
            combine current (Eq (Le_PVar x, value))
          ) values, [false_f]   
                              
        | [] -> 
          let values = try 
            let v = Le_Var (fresh_e()) in
            observe_state current v (Spec_Fun_Specs.get_value_vref_lg le1 v) data
           with SymExecException _ -> [] in
                            
           begin match values with     
             | value :: rest ->
               (* variable reference lg *)
                List.map (fun value ->
                    combine current (Eq (Le_PVar x, value))
                ) values, [false_f] 
                              
             | [] -> continue le1
                                                                                    
           end
                                          
        end in              
                        
    match sf with
      | GetValue e1 ->       
        begin
          let le1 = expr_to_logical_expr e1 in  
          match le1 with
					  | Le_Var _
					  | Le_PVar _ ->
              begin
               (* check if le1 is not a reference *)
               if (CoreStar_Frontend_Pulp.implies current (Spec_Fun_Specs.get_value_not_a_ref_pre le1)) then [combine current (Eq (Le_PVar x, le1))], [false_f]
               else begin (* ref *)
							          
                   if (CoreStar_Frontend_Pulp.implies current (Spec_Fun_Specs.get_value_unresolvable_ref_pre le1)) then [false_f], [excep_post ()]
                   else  var_ref_cases le1 mem_ref_cases
                   
               end (* ref *)
              
              end
              
            | Le_Ref (l, x, t) -> 
              begin match l with 
                | Le_Literal Undefined -> [false_f], [excep_post ()]
                | _ -> 
                  begin match t with
                    | VariableReference -> var_ref_cases le1 (fun _ -> raise (SymExecException ("Not Implemented Branching in GetValue", data.src_offset)))
                    | MemberReference -> mem_ref_cases le1
                  end
              end
	  			  | Le_Literal _ | Le_UnOp _ | Le_BinOp _ |  Le_Base _ | Le_Field _ -> [combine current (Eq (Le_PVar x, le1))], [false_f]
					  | Le_None | Le_TypeOf _ -> raise (SymExecException ("Wrong Parameter to GetValue", data.src_offset))
        end    

      | sp -> raise (NotImplemented (Pulp_Syntax_Print.string_of_spec_fun_id sp))
  
let execute_proto_field current e1 e2 data =
  let ls = Le_Var (fresh_e ()) in
  let l = Le_Var (fresh_e ()) in
  let v = Le_Var (fresh_e ()) in
  let pi = proto_pred_f ls e1 e2 l v in
  observe_state current v pi data
  
 
let rec execute_stmt f sg cfg fs env spec_env snode_id cmd_st_tbl = 
  let contradiction id =
    let new_sn = StateG.mk_node sg (mk_sg_node id false_f) in
    Hashtbl.add cmd_st_tbl id new_sn;
    StateG.mk_edge sg snode_id new_sn () in
         
 
  (* Hashtable cfg_node -> state_node list for termination *)
  let new_snode id state =
    let new_sn = StateG.mk_node sg (mk_sg_node id state) in
    Hashtbl.add cmd_st_tbl id new_sn;
    StateG.mk_edge sg snode_id new_sn ();
    execute_stmt f sg cfg fs env spec_env new_sn cmd_st_tbl in
    
  let new_snodes_cond id1 id2 state e =
   
    let exprs_true = get_proof_cases_eq_true e in
    (*Printf.printf "True cases: %s" (String.concat "\n\n\n" (List.map Pulp_Logic_Print.string_of_formula exprs_true));*)
    
    let implies_true = 
      List.exists (fun expr_true -> 
        try CoreStar_Frontend_Pulp.implies state expr_true 
        with CoreStar_Frontend_Pulp.ContradictionFound -> Printf.printf "Contradiction found"; false
      ) exprs_true in
    Printf.printf "Guarded Goto Implies True? %b" implies_true; 
    if (implies_true) then new_snode id1 state   
    else begin
      
      let exprs_false = get_proof_cases_eq_false e in
      Printf.printf "False cases: %s" (String.concat "\n\n\n" (List.map Pulp_Logic_Print.string_of_formula exprs_false));
      let implies_false = List.exists (fun expr_false -> 
        try CoreStar_Frontend_Pulp.implies state expr_false
        with CoreStar_Frontend_Pulp.ContradictionFound -> Printf.printf "Contradiction found"; false 
      ) exprs_false in 
      Printf.printf "Guarded Goto Implies False? %b" implies_false; 
      if (implies_false) then new_snode id2 state 
      else begin
    
        Printf.printf "Guarded Goto true"; 
        List.iter (fun expr_true ->     
          let state_true = combine expr_true state in
          Format.pp_print_flush(Format.std_formatter)();
          Printf.printf "Guarded Goto true state %s" (Pulp_Logic_Print.string_of_formula expr_true); 
          Printf.printf "Guarded Goto true state %s" (Pulp_Logic_Print.string_of_formula state_true); 
          
          try new_snode id1 state_true       
          with CoreStar_Frontend_Pulp.ContradictionFound -> Printf.printf "Contradiction found"; contradiction id1
            
        ) exprs_true;
            
         Printf.printf "Guarded Goto false"; 
         List.iter (fun expr_false ->     
          let state_false = combine expr_false state in
          Format.pp_print_flush(Format.std_formatter)();
          Printf.printf "Guarded Goto false state %s" (Pulp_Logic_Print.string_of_formula expr_false);  
          Printf.printf "Guarded Goto true state %s" (Pulp_Logic_Print.string_of_formula state_false);    
          
          try new_snode id2 state_false
          with CoreStar_Frontend_Pulp.ContradictionFound -> Printf.printf "Contradiction found"; contradiction id2
          
        ) exprs_false;        
 
     end 
    end in

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
        
  let symbexec_call call_f funcs x =
      let succ1, succ2 = get_two_succs snode.sgn_id in
      let edge1 = CFG.get_edge_data cfg snode.sgn_id succ1 in
      let edge2 = CFG.get_edge_data cfg snode.sgn_id succ2 in
      
      let post_normal, post_excep = call_f x funcs snode.sgn_state in
      (*List.iter (fun post -> Printf.printf "Normal Postcondition %s \n" (Pulp_Logic_Print.string_of_formula post)) post_normal;
      List.iter (fun post -> Printf.printf "Excep Postcondition %s \n" (Pulp_Logic_Print.string_of_formula post)) post_excep;*)

      List.iter2 (new_snode_call succ1 edge1) post_normal post_excep;
      List.iter2 (new_snode_call succ2 edge2) post_normal post_excep in
  
  Printf.printf "********Execute Stmt %s *********\n" (Pulp_Syntax_Print.string_of_statement stmt);
  
  match stmt.stmt_stx with
    | Label l -> 
      if l = f.func_ctx.label_return || l = f.func_ctx.label_throw 
      then () 
      else begin
        (* Loop heads are on the label commands *)
        
        if stmt.stmt_data.loop_head then begin
          
          let posts_nodes = Hashtbl.find_all cmd_st_tbl snode.sgn_id in
          let implies_node = 
            try Some (List.find (fun post -> 
	            if post = snode_id then false 
	            else
	            let st = StateG.get_node_data sg post in
	            CoreStar_Frontend_Pulp.implies snode.sgn_state st.sgn_state
	          ) posts_nodes) 
            with Not_found -> None in
          
          match implies_node with
            | None -> begin 
	             let stmt = CFG.get_node_data cfg snode.sgn_id in
	             let invariants = Pulp_Formula_Parser_Utils.get_inv_from_code stmt.stmt_data.stmt_annots in
	          
	             let posts = List.map (fun inv -> 
	               Printf.printf "\n Invariant: %s\n" (Pulp_Logic_Print.string_of_formula inv); 
                 let frames = CoreStar_Frontend_Pulp.frame snode.sgn_state inv in
	               match frames with
                  | Some [frame] -> Some (combine frame (CoreStar_Frontend_Pulp.existential_to_universals inv))
                  | Some _ -> raise (NotImplemented "Multiple frames")
                  | None -> None
	             ) invariants in
	            
	             let post = try List.find (fun p -> p != None) posts with Not_found -> raise (SymExecException ("Loop invariant does't hold", stmt.stmt_data.src_offset)) in
	             
	             begin match post with
	               | Some post -> new_snode (get_single_succ snode.sgn_id) post
	               | None -> raise Utils.CannotHappen
	             end                    
             end     
            | Some nd -> (* We do not need to continue this path anymore *) (*StateG.mk_edge sg snode_id nd*) ();
     
        end 
        else new_snode (get_single_succ snode.sgn_id) snode.sgn_state
      end
      
      
      
    | Goto l -> new_snode (get_single_succ snode.sgn_id) snode.sgn_state
    
    | GuardedGoto (e, l1, l2) -> 
      let succ1, succ2 = get_two_succs snode.sgn_id in
      let edge1 = CFG.get_edge_data cfg snode.sgn_id succ1 in
      let edge2 = CFG.get_edge_data cfg snode.sgn_id succ2 in
      
      let succTrue, succFalse =
        match edge1, edge2 with 
          | Simp_Common.Edge_True, Simp_Common.Edge_False -> succ1, succ2
          | Simp_Common.Edge_False, Simp_Common.Edge_True -> succ2, succ1
          | _, _ -> raise (Invalid_argument "Expected true and false edges") in
      
      new_snodes_cond succTrue succFalse snode.sgn_state (expr_to_logical_expr e);
      
    | Basic (Assignment {assign_left = x; assign_right = (Expression e)}) ->
      
      let id = get_single_succ snode.sgn_id in
      let old = fresh_e () in
      let logic_e = expr_to_logical_expr e in
      
      let logic_e = match logic_e with
        | Le_BinOp (le1, Comparison LessThan, le2) 
        | Le_BinOp (le1, Comparison LessThanEqual, le2) ->
          begin
            let implies_true = try CoreStar_Frontend_Pulp.implies snode.sgn_state (eq_true logic_e) 
            with CoreStar_Frontend_Pulp.ContradictionFound -> Printf.printf "Contradiction found"; false in
            if implies_true then Le_Literal (Bool true)
            else begin
              let implies_false = try CoreStar_Frontend_Pulp.implies snode.sgn_state (eq_false logic_e) 
              with CoreStar_Frontend_Pulp.ContradictionFound -> Printf.printf "Contradiction found"; false in
              if implies_false then Le_Literal (Bool false)
              else logic_e
            end
          end
        | _ -> logic_e in
      
      let varmap = ProgramVarMap.add x (Le_Var old) ProgramVarMap.empty in    
      let post = combine (Eq (Le_PVar x, subs_pvar_in_exp x (Le_Var old) logic_e)) (subs_pvars varmap snode.sgn_state) in
      let post = CoreStar_Frontend_Pulp.elim_vars_in_formula post in 
      
      new_snode id post 
              
    | Basic (Assignment {assign_left = x; assign_right = (Call c)}) ->  
      symbexec_call (execute_normal_call_stmt c stmt.stmt_data false) (AllFunctions.fold AllFunctions.add env fs) x
    | Basic (Assignment {assign_left = x; assign_right = (Eval c)})   
    | Basic (Assignment {assign_left = x; assign_right = (BuiltinCall c)}) -> 
      symbexec_call (execute_normal_call_stmt c stmt.stmt_data true) (AllFunctions.fold AllFunctions.add env fs) x
      
    | Basic (Assignment {assign_left = x; assign_right = (ProtoF (e1, e2))}) -> 
      Printf.printf "Execute protoField \n";
      let id = get_single_succ snode.sgn_id in
      let values = execute_proto_field snode.sgn_state (expr_to_logical_expr e1) (expr_to_logical_expr e2) stmt.stmt_data in
      Printf.printf "GotValues \n";
      List.iter (fun value ->
        let post = combine snode.sgn_state (Eq (Le_PVar x, value)) in
        new_snode id post
      ) values
      
    | Basic (Assignment {assign_right = (ProtoO (e1, e2))}) -> raise (NotImplemented "ProtoObj")
     
    | Basic bs -> 
        let id = get_single_succ snode.sgn_id in
        begin try
          let post = execute_basic_stmt bs stmt.stmt_data snode.sgn_state in
          new_snode id post 
        with CoreStar_Frontend_Pulp.ContradictionFound ->
          contradiction id
        end
        
    | Sugar s -> 
      begin match s with
        | SpecFunction (x, sf, l) -> symbexec_call (execute_spec_func_call_stmt sf stmt.stmt_data) spec_env x      
        | If _ -> raise (Invalid_argument "Symbolic execution does not work on syntactic sugar")
      end


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
let execute f cfg fs spec_env spec =
  let label_map = get_all_labels cfg in (* Something not right in the interface *)
  
  let start = Hashtbl.find label_map (f.func_ctx.label_entry) in
  
  (* cfg_node -> state_node list *)
  let cmd_st_tbl = Hashtbl.create 100 in
  
  (* state graph *)
  let sg = StateG.mk_graph () in
  let params_not_none = Star (List.map (fun p -> NEq (Le_PVar p, Le_None)) f.func_params) in 
  
  let params_not_empty = match f.func_type with
    | Procedure_User 
    | Procedure_Spec -> Star (List.map (fun p -> NEq (Le_PVar p, Le_Literal Empty)) f.func_params)
    | Procedure_Builtin -> empty_f in 

  let params_not_a_ref = match f.func_type with
    | Procedure_User
    | Procedure_Builtin -> Star (List.map (fun p -> type_of_not_a_ref_f (Le_PVar p)) f.func_params)
    | Procedure_Spec -> empty_f in 
  
  let pre = combine spec.spec_pre params_not_none in
  let pre = combine pre params_not_empty in
  let pre = combine pre params_not_a_ref in
  let first = StateG.mk_node sg (mk_sg_node start pre) in
  
  Hashtbl.add cmd_st_tbl start first;
  
  let env_builtin = Environment.get_env() in
  
  try 
    execute_stmt f sg cfg fs env_builtin spec_env first cmd_st_tbl;
    sg, cmd_st_tbl 
  with SymExecException (msg, src_offset) -> 
    raise (SymExecExcepWithGraph (msg, src_offset, sg))
  
  
let check_post f cfg fs sg cmd_st_tbl spec_env spec =
  let posts, throw_posts = get_posts f cfg sg cmd_st_tbl in
  let spec_post = List.map (change_return f.func_ctx.return_var) spec.spec_post in     
  let spec_excep_post = List.map (change_return f.func_ctx.throw_var) spec.spec_excep_post in
  ((List.for_all (fun post -> CoreStar_Frontend_Pulp.implies_or_list (simplify post) spec_post) posts)
  && (List.for_all (fun post -> CoreStar_Frontend_Pulp.implies_or_list (simplify post) spec_excep_post) throw_posts))
  

(* To separate printing from executing *)  
let execute_all (f : function_block) (fs : function_block AllFunctions.t) spec_env path = 
  let cfg = fb_to_cfg f in
  List.for_all (fun spec -> 
    let sg, cmd_st_tbl = 
    try 
      execute f cfg fs (Spec_Fun_Specs.get_env_spec()) spec 
    with SymExecExcepWithGraph (msg, src_offset, sg) -> 
      print_state_graph sg cfg f.func_name path;
      raise (SymExecException (msg, src_offset)) in
      
    print_state_graph sg cfg f.func_name path; 
      
    check_post f cfg fs sg cmd_st_tbl spec_env spec
  ) f.func_spec