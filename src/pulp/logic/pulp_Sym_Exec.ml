open Pulp_Syntax
open Pulp_Procedure
open State_Graph
open Control_Flow
open Pulp_Logic
open Pulp_Logic_Rules
open Pulp_Logic_Utils

exception NotImplemented of string

exception SymExecException of string
exception SymExecExcepWithGraph of string * StateG.graph

let execute_basic_stmt bs pre : formula =
  Printf.printf "Execute Basic Stmt \n" ;
  (*Printf.printf "Precondition %s \n" (Pulp_Logic_Print.string_of_formula pre);*)
  (* pre => pre_stmt' * F*)
  (* post_stmt' * F *)
  
  let cmd_pre, cmd_post = small_axiom_basic_stmt bs in
  Printf.printf "Got spec for Basic Stmt \n" ;
  
  let posts =       
    try CoreStar_Frontend_Pulp.apply_spec pre cmd_pre cmd_post
    with CoreStar_Frontend_Pulp.ContradictionFound -> raise (SymExecException "Contradiction found in basic stmt") in
  
  Printf.printf "Got Postcondition \n" ;

  
  match posts with
    | None -> 
      begin 
        Printf.printf "Could Not Apply Spec";
        raise (SymExecException "CouldNotApplySpec") 
      end
    | Some posts ->
      begin match posts with 
        | [] -> 
          Printf.printf "Contradiction Found";
          raise (SymExecException "Contradiction Found")
        | [post] -> 
          begin 
            Printf.printf "Postcondition %s \n" (Pulp_Logic_Print.string_of_formula post);
            post
          end
        | posts -> 
          List.iter (fun post -> Printf.printf "Postcondition %s \n" (Pulp_Logic_Print.string_of_formula post)) posts;
          raise (NotImplemented "Multiple frames")
      end
      

let execute_call_stmt varmap x fid fb fs current : formula list * formula list =
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
       with CoreStar_Frontend_Pulp.ContradictionFound -> raise (SymExecException "Contradiction found in function call")
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
      | [] -> [false_f]
      | posts -> posts in
  
  let f_spec = fb.func_spec in
  let posts_normal = get_posts fb f_spec false in
  let posts_excep = get_posts fb f_spec true in
  posts_normal, posts_excep
      
let execute_normal_call_stmt c is_builtin x fs current : formula list * formula list =
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
    
  execute_call_stmt varmap x fid fb fs current
  
let observe_state current v pre =
  let posts = 
    try CoreStar_Frontend_Pulp.apply_spec current pre (combine pre (REq v))
    with CoreStar_Frontend_Pulp.ContradictionFound -> raise (SymExecException "Contradiction found in basic stmt") in
  let posts = match posts with
    | None -> raise (SymExecException "Observing State No Postcondition Found")
    | Some posts -> posts in
  let values = List.map get_return posts in 
  let values = List.fold_left (fun result v -> match v with 
    | None -> result
    | Some v -> v :: result) [] values in
  match values with
    | [] -> raise (SymExecException "Observing State No Return Found")
    | _ -> values

(* returns the list of normal post conditions and exceptional post conditions *)    
let execute_spec_func_call_stmt sf x fs current : formula list * formula list =
  (*let current = forget_return current in
  let current = CoreStar_Frontend_Pulp.elim_vars_in_formula current in*)
    match sf with
      | GetValue e1 ->       
        begin
          let le1 = expr_to_logical_expr e1 in
           
          (* check if le1 is not a reference *)
          
          let not_a_ref = match le1 with
	            | Le_Var _
	            | Le_PVar _ -> CoreStar_Frontend_Pulp.implies current (type_of_not_a_ref_f le1)
	            | Le_None | Le_TypeOf _ -> raise (SymExecException "Wrong Parameter to GetValue")
	            | Le_Literal _ | Le_UnOp _ | Le_BinOp _ |  Le_Base _ | Le_Field _ -> true
	            | Le_Ref _ -> false in

          if (not_a_ref) then [combine current (Eq (Le_PVar x, le1))], [false_f]
          else begin
            
            (* check if le1 is a reference *)
            
            let is_a_ref = match le1 with
                | Le_Var _
                | Le_PVar _ -> CoreStar_Frontend_Pulp.implies current (type_of_ref_f le1)
                | Le_None | Le_TypeOf _ -> raise (SymExecException "Wrong Parameter to GetValue")
                | Le_Literal _ | Le_UnOp _ | Le_BinOp _ |  Le_Base _ | Le_Field _ -> false
                | Le_Ref _ -> true in

            if (is_a_ref) then begin
              
               (* check if base(le1) is undefined *)
              
               
               let is_unresolved_ref = match le1 with
                 | Le_Ref (Le_Literal Undefined, _, _) -> true
                 | Le_Ref (Le_PVar _, _, _) | Le_Ref (Le_Var _, _, _) | Le_Var _ | Le_PVar _ -> CoreStar_Frontend_Pulp.implies current (Eq (Le_Base le1, Le_Literal Undefined))
                 | _ -> false in


               if (is_unresolved_ref) then begin
                  let lerror = Le_Var (fresh_e()) in
								  let post_unresolvable_ref = combine current
								    (Star [
								      Eq (Le_PVar x, lerror);
								      proto_heaplet_f lerror (Le_Literal (LLoc Lrep));
								      class_heaplet_f lerror "Error"
								    ]) in [false_f], [post_unresolvable_ref]
                end
                
                else begin 
                  let is_v_ref = match le1 with
	                 | Le_Ref (_, _, VariableReference) -> true
	                 | Le_Var _ | Le_PVar _ -> CoreStar_Frontend_Pulp.implies current (type_of_vref_f le1)
	                 | _ -> false in
                  
	                if (is_v_ref) then begin
                    let v = Le_Var (fresh_e()) in
										let pre_vref_obj = Star [
										  NEq (Le_Base le1, Le_Literal (LLoc Lg));
										  Heaplet (Le_Base le1, Le_Field le1, v);
										  NEq (v, Le_None) 
										] in
                                    
                    let values = try 
                      observe_state current v pre_vref_obj
                    with SymExecException _ -> [] in
                    
                    begin match values with
                      | [] ->
                        
                        (* check if variable reference lg *)
                        
											 let ls = Le_Var (fresh_e()) in
											 let l = Le_Var (fresh_e()) in 
                       let v = Le_Var (fresh_e()) in
											 let pre_vref_lg = combine
											    (proto_pred_f ls (Le_Literal (LLoc Lg)) (Le_Field le1) l v)
											    (Star [
											    Eq (Le_Base le1, Le_Literal (LLoc Lg));
											    NEq (v, Le_Literal Empty) 
											  ]) in
                                
		                    let values = try 
		                      observe_state current v pre_vref_lg
		                    with SymExecException _ -> [] in
                        
                        begin match values with
                          | [] ->
                             raise (SymExecException "Not Implemented Branching in GetValue for Variable Reference")
                            
                          | _ ->
                            
                            (* variable reference lg *)
                            List.map (fun value ->
                                combine current (Eq (Le_PVar x, value))
                            ) values, [false_f]                            
                            
                        end

                      | _ -> 
                        begin
                          
                        (* variable reference not lg *)
                        List.map (fun value ->
                           combine current (Eq (Le_PVar x, value))
                        ) values, [false_f]
                          
                        end
                        
                     end (* end match values with*)

                  end
	                else begin 
                     (* TODO : check if mem reference first *)
		                 (* TODO : base le1 = String / Number / Boolean *)
		                

		                 begin
		                     let ls = Le_Var (fresh_e()) in
		                     let l = Le_Var (fresh_e()) in 
		                     let v = Le_Var (fresh_e()) in
		                     let pre_mref_not_empty = combine 
		                        (proto_pred_f ls (Le_Base le1) (Le_Field le1) l v)
		                        (Star [
		                        type_of_mref_f le1; 
		                        type_of_obj_f (Le_Base le1);
		                        NEq (v, Le_Literal Empty) 
		                      ]) in            
                         let values = try 
                              observe_state current v pre_mref_not_empty
                            with SymExecException _ -> [] in
                        
                         begin match values with
		                       | [] -> 
                             (* check if member reference object empty *)
                             let ls = Le_Var (fresh_e()) in
                             let l = Le_Var (fresh_e()) in 
                             let v = Le_Var (fresh_e()) in
                             let pre_mref_empty = combine
                               (proto_pred_f ls (Le_Base le1) (Le_Field le1) l v)   
                               (Star [
                               type_of_mref_f le1; 
                               type_of_obj_f (Le_Base le1);
                               Eq (v, Le_Literal Empty)]) in
                        
                             if (CoreStar_Frontend_Pulp.implies current pre_mref_empty) then 
                               [combine current (Eq (Le_PVar x, Le_Literal Undefined))], [false_f] 
                             else raise (SymExecException "Not Implemented Branching in GetValue for Reference")
		                       
                          | _ ->
		                        (* member reference not empty *)
		                        List.map (fun value ->
		                          combine current (Eq (Le_PVar x, value))
		                        ) values, [false_f]  
		                     end
		                 end (* else pre_mref_empty *)
                  end (* else is_v_ref *)
                  
                 end (* else unresolved ref *)

                
              
            end (* is_a_ref *)
            else begin (* TODO : branch all possible ways *)
                raise (SymExecException "Not Implemented Branching in GetValue for Any Value")
            end 
          end (* not_a_ref *)
        
        end

      | sp -> raise (NotImplemented (Pulp_Syntax_Print.string_of_spec_fun_id sp))
  
let execute_proto_field current e1 e2 =
  let ls = Le_Var (fresh_e ()) in
  let l = Le_Var (fresh_e ()) in
  let v = Le_Var (fresh_e ()) in
  let pi = proto_pred_f ls e1 e2 l v in
  observe_state current v pi
  
 
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
    
    let implies_true = List.exists (fun expr_true -> CoreStar_Frontend_Pulp.implies state expr_true) exprs_true in
    Printf.printf "Guarded Goto Implies True? %b" implies_true; 
    if (implies_true) then new_snode id1 state   
    else begin
      
      let exprs_false = get_proof_cases_eq_false e in
      let implies_false = List.exists (fun expr_false -> CoreStar_Frontend_Pulp.implies state expr_false) exprs_false in 
      Printf.printf "Guarded Goto Implies False? %b" implies_false; 
      if (implies_false) then new_snode id2 state 
      else begin
    
        Printf.printf "Guarded Goto true"; 
        List.iter (fun expr_true ->     
          let state_true = combine expr_true state in
          Format.pp_print_flush(Format.std_formatter)();
          Printf.printf "Guarded Goto true state %s" (Pulp_Logic_Print.string_of_formula expr_true); 
          Printf.printf "Guarded Goto true state %s" (Pulp_Logic_Print.string_of_formula state_true); 
          new_snode id1 state_true       
        ) exprs_true;
            
         Printf.printf "Guarded Goto false"; 
         List.iter (fun expr_false ->     
          let state_false = combine expr_false state in
          Format.pp_print_flush(Format.std_formatter)();
          Printf.printf "Guarded Goto false state %s" (Pulp_Logic_Print.string_of_formula expr_false);  
          Printf.printf "Guarded Goto true state %s" (Pulp_Logic_Print.string_of_formula state_false);    
          new_snode id2 state_false
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
  
  match stmt with
    | Label l -> 
      if l = f.func_ctx.label_return || l = f.func_ctx.label_throw 
      then () 
      else new_snode (get_single_succ snode.sgn_id) snode.sgn_state
      
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
      
      let varmap = ProgramVarMap.add x (Le_Var old) ProgramVarMap.empty in    
      let post = combine (Eq (Le_PVar x, subs_pvar_in_exp x (Le_Var old) logic_e)) (subs_pvars varmap snode.sgn_state) in
      let post = CoreStar_Frontend_Pulp.elim_vars_in_formula post in 
      
      new_snode id post 
              
    | Basic (Assignment {assign_left = x; assign_right = (Call c)}) ->  
      symbexec_call (execute_normal_call_stmt c false) (AllFunctions.fold AllFunctions.add env fs) x
    | Basic (Assignment {assign_left = x; assign_right = (Eval c)})   
    | Basic (Assignment {assign_left = x; assign_right = (BuiltinCall c)}) -> 
      symbexec_call (execute_normal_call_stmt c true) (AllFunctions.fold AllFunctions.add env fs) x
      
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
        
    | Sugar s -> 
      begin match s with
        | SpecFunction (x, sf, l) -> symbexec_call (execute_spec_func_call_stmt sf) spec_env x      
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
  
  let env = Environment.get_env() in
  
  try 
    execute_stmt f sg cfg fs env spec_env first cmd_st_tbl;
    sg, cmd_st_tbl 
  with SymExecException msg -> 
    raise (SymExecExcepWithGraph (msg, sg))
  
  
let execute_check_post f cfg fs spec_env spec =
  let sg, cmd_st_tbl = execute f cfg fs spec_env spec in
  let posts, throw_posts = get_posts f cfg sg cmd_st_tbl in
  List.for_all (fun post -> CoreStar_Frontend_Pulp.implies_or_list (simplify post) spec.spec_post) posts
  
let execute_all (f : function_block) (fs : function_block AllFunctions.t) spec_env = 
  let cfg = fb_to_cfg f in
  List.iter (fun spec -> ignore (execute f cfg fs spec_env spec)) f.func_spec