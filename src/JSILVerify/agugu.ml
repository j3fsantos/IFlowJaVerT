
		print_time_debug ("check_pred_def:");
		let _, pred_def, pred_def_up = Array.get pred_defs index in
		print_debug (Printf.sprintf "----------------------------");
		print_debug (Printf.sprintf "Current pred symbolic state: %s" (Symbolic_State_Print.string_of_symb_state pred_def));
		
		let unifier = try (Some (Spatial_Entailment.unify_symb_states_fold pred_name existentials pred_def_up pred_def symb_state_caller))
			with | Spatial_Entailment.UnificationFailure _ -> None in
		
		(match unifier with
		| Some ((framed_heap, framed_preds, subst, pf_discharges, new_gamma), _, None) ->
		  	(* Fold Complete *)

		  	(* Remove from the symb_state the spatial resources corresponding to the folded predicate *)
		  	let new_symb_state = update_symb_state_after_folding symb_state framed_heap framed_preds pf_discharges new_gamma in
			
		  	(* Print useful INFO *)
			print_debug (Printf.sprintf "Folding Complete!");
			print_debug (Printf.sprintf "Symbolic state after FOLDING:\n%s" (Symbolic_State_Print.string_of_symb_state new_symb_state));
			Some (new_symb_state, new_spec_vars, search_info)

		| Some ((framed_heap, framed_preds, subst, pf_discharges, new_gamma), existentials, Some (missing_pred_name, missing_pred_args) ) 
				when missing_pred_name = pred_name ->
			
			print_debug (Printf.sprintf "Folding Incomplete. Missing %s(%s)\n"
				pred_name (String.concat ", " (List.map JSIL_Print.string_of_logic_expression missing_pred_args)));
		
			(* Fold Incomplete - Must recursively fold the predicate *)
			let new_symb_state, missing_pred_args, existentials' = 
				process_missing_pred_assertion missing_pred_args subst existentials symb_state framed_heap framed_preds pf_discharges new_gamma in 
			fold_predicate predicates pred_name pred_defs new_symb_state params missing_pred_args new_spec_vars (Some existentials') search_info

		| _ -> 
			(* Fold Failed - we try to fold again removing a recursive call to the predicate from 
			   the predicate definition  *)
			print_debug (Printf.sprintf "Folding Failed."); 	

			let preds_pred_def  = (ss_preds pred_def) in 
			let preds_pred_def' = preds_copy preds_pred_def in 
			(match preds_remove_by_name preds_pred_def' pred_name with 
			| None -> None 
			| Some (_, missing_pred_args) -> (
				print_debug (Printf.sprintf "Going to remove %s(%s) and try to fold again"
					pred_name (String.concat ", " (List.map JSIL_Print.string_of_logic_expression missing_pred_args)));

				let pred_def' = ss_replace_preds pred_def preds_pred_def' in
				let unifier = try (Some (Spatial_Entailment.unify_symb_states_fold pred_name existentials (Normaliser.create_unification_plan ?predicates_sym:(Some predicates) pred_def' SS.empty) pred_def' symb_state_caller))
					with | Spatial_Entailment.UnificationFailure _ -> None in

				(match unifier with
				| Some ((framed_heap, framed_preds, subst, pf_discharges, new_gamma), new_existentials, None) ->
		  			(* We were able to fold the predicate up to a recursive call  *)
		  			(* Now we need to fold the recursive call                     *)

		  			let new_symb_state = update_symb_state_after_folding symb_state framed_heap framed_preds pf_discharges new_gamma in
		  			let new_symb_state', missing_pred_args, existentials' = 
						process_missing_pred_assertion missing_pred_args subst (SS.union existentials new_existentials) new_symb_state framed_heap framed_preds pf_discharges new_gamma in 
					fold_predicate predicates pred_name pred_defs new_symb_state' params missing_pred_args new_spec_vars (Some existentials') search_info

		  		| _ -> None)))) in


	let pred_def_indexes  = Array.to_list (Array.init (Array.length pred_defs) (fun i -> i)) in 
	List.fold_left (fun ac i -> if (ac = None) then fold_predicate_aux i else ac) None pred_def_indexes







	let process_missing_pred_assertion
			(missing_pred_args : jsil_logic_expr list)  (subst : substitution) (existentials : SS.t)
			(symb_state : symbolic_state) (framed_heap : SHeap.t) (framed_preds : predicate_set) 
			(pf_discharges : jsil_logic_assertion list) (new_gamma : TypEnv.t) : symbolic_state * (jsil_logic_expr list) * SS.t = 
		
		let missing_pred_args = List.map (JSIL_Logic_Utils.lexpr_substitution subst false) missing_pred_args in
				
		(* 1. Remove from the symb_state the spatial resources corresponding to the folded predicate *)
		let new_symb_state          = update_symb_state_after_folding symb_state framed_heap framed_preds pf_discharges new_gamma in
				
		(* 2. After folding, we may be able to determine the exact expressions for some of the
			existentials. These existentials cease to be existentials. We need to substitute 
			them on the symb_state and on the arguments for the missing predicate assertion  *)
		let new_symb_state, e_subst = Simplifications.simplify_ss_with_subst new_symb_state (Some None) in
		let e_subst                 = filter_substitution (fun v le -> (SS.inter existentials (get_lexpr_lvars le)) = SS.empty) e_subst in 				
		let e_subst_domain          = get_subst_vars (fun x -> false) e_subst in 
		let existentials'           = SS.filter (fun v -> (not (SS.mem v e_subst_domain))) existentials in
		let e_subst'                = filter_substitution_set existentials' e_subst in				
		let new_symb_state          = ss_substitution e_subst' true new_symb_state in
		let missing_pred_args       = List.map (fun le -> JSIL_Logic_Utils.lexpr_substitution e_subst' true le) missing_pred_args in
				
		(* Print useful INFO *)
		(* print_debug (Printf.sprintf "Old exists: %s" (String.concat "," (SS.elements existentials)));
		print_debug (Printf.sprintf "New subst: %s" (Symbolic_State_Print.string_of_substitution e_subst'));
		print_debug (Printf.sprintf "New exists: %s" (String.concat "," (SS.elements existentials')));
		print_debug (Printf.sprintf "Missing %s(%s)!!!"
			pred_name (String.concat ", " (List.map (fun le -> JSIL_Print.string_of_logic_expression le false) missing_pred_args)));
		print_debug (Printf.sprintf "Symbolic state after partial FOLDING:\n%s" (Symbolic_State_Print.string_of_shallow_symb_state new_symb_state)); *)
		
		new_symb_state, missing_pred_args, existentials' in 		


	(*  Step 0: create a symb_state with the appropriate calling store
	    --------------------------------------------------------------
	    * Create the symbolic store mapping the formal arguments of the 
	      predicate to be folded to the corresponding logical expressions
	    * Create a new symb_state with the new calling store    *)


	print_debug_petar ("Inside fold_predicate.");
	print_debug_petar (Printf.sprintf "Arguments: %s" (String.concat ", " (List.map (fun x -> JSIL_Print.string_of_logic_expression x) args)));
	let new_store         = SStore.init params args in
	let symb_state_caller = ss_replace_store symb_state new_store in


	(* Step 1: compute the existentials
	    --------------------------------------------------------------
		* the existentials are the new logical variables used in the logical 
		  expressions given as parameters to the fold 
		  e.g. fold(#x, #y) if #y is not a spec var, then it is an existential 
		* the spec vars need to be updated with the existentials 
	*)
	let existentials =
		(match existentials with
		| None ->
			let symb_state_vars : SS.t = ss_lvars symb_state  in
			let args_vars       : SS.t = get_lexpr_list_lvars args in
			let existentials    : SS.t = SS.diff args_vars symb_state_vars in
			existentials
		| Some existentials -> existentials) in
	let new_spec_vars = SS.union spec_vars existentials in
	(* print_debug (Printf.sprintf "New spec vars (fold): %s" (String.concat ", " (SS.elements existentials))); *)

	(* Printing useful info *)
	let existentials_str = print_var_list (SS.elements existentials) in
	print_debug (Printf.sprintf ("\nFOLDING %s(%s) with the existentials %s in the symbolic state: \n%s\n")
	  pred_name
		(String.concat ", " (List.map JSIL_Print.string_of_logic_expression args))
		existentials_str
		(Symbolic_State_Print.string_of_symb_state symb_state));

	let rec one_step_fold  
			(index : int) 
			(search_info : symbolic_execution_context) : (symbolic_state * SS.t * symbolic_execution_context) option =
		
		print_time_debug ("check_pred_def:");
		let _, pred_def, pred_def_up = Array.get pred_defs index in
		print_debug (Printf.sprintf "----------------------------");
		print_debug (Printf.sprintf "Current pred symbolic state: %s" (Symbolic_State_Print.string_of_symb_state pred_def));
		
		let unifier = try (Some (Spatial_Entailment.unify_symb_states_fold pred_name existentials pred_def_up pred_def symb_state_caller))
			with | Spatial_Entailment.UnificationFailure _ -> None in
		
		(match unifier with
		| Some ((framed_heap, framed_preds, subst, pf_discharges, new_gamma), _, None) ->
		  	(* Fold Complete *)

		  	(* Remove from the symb_state the spatial resources corresponding to the folded predicate *)
		  	let new_symb_state = update_symb_state_after_folding symb_state framed_heap framed_preds pf_discharges new_gamma in
			
		  	(* Print useful INFO *)
			print_debug (Printf.sprintf "Folding Complete!");
			print_debug (Printf.sprintf "Symbolic state after FOLDING:\n%s" (Symbolic_State_Print.string_of_symb_state new_symb_state));
			Some (new_symb_state, new_spec_vars, search_info)

		| Some ((framed_heap, framed_preds, subst, pf_discharges, new_gamma), existentials, Some (missing_pred_name, missing_pred_args) ) 
				when missing_pred_name = pred_name ->
			
			print_debug (Printf.sprintf "Folding Incomplete. Missing %s(%s)\n"
				pred_name (String.concat ", " (List.map JSIL_Print.string_of_logic_expression missing_pred_args)));
		
			(* Fold Incomplete - Must recursively fold the predicate *)
			let new_symb_state, missing_pred_args, existentials' = 
				process_missing_pred_assertion missing_pred_args subst existentials symb_state framed_heap framed_preds pf_discharges new_gamma in 
			fold_predicate predicates pred_name pred_defs new_symb_state params missing_pred_args new_spec_vars (Some existentials') search_info

		| _ -> 
			(* Fold Failed - we try to fold again removing a recursive call to the predicate from 
			   the predicate definition  *)
			print_debug (Printf.sprintf "Folding Failed."); 	

			let preds_pred_def  = (ss_preds pred_def) in 
			let preds_pred_def' = preds_copy preds_pred_def in 
			(match preds_remove_by_name preds_pred_def' pred_name with 
			| None -> None 
			| Some (_, missing_pred_args) -> (
				print_debug (Printf.sprintf "Going to remove %s(%s) and try to fold again"
					pred_name (String.concat ", " (List.map JSIL_Print.string_of_logic_expression missing_pred_args)));

				let pred_def' = ss_replace_preds pred_def preds_pred_def' in
				let unifier = try (Some (Spatial_Entailment.unify_symb_states_fold pred_name existentials (Normaliser.create_unification_plan ?predicates_sym:(Some predicates) pred_def' SS.empty) pred_def' symb_state_caller))
					with | Spatial_Entailment.UnificationFailure _ -> None in

				(match unifier with
				| Some ((framed_heap, framed_preds, subst, pf_discharges, new_gamma), new_existentials, None) ->
		  			(* We were able to fold the predicate up to a recursive call  *)
		  			(* Now we need to fold the recursive call                     *)

		  			let new_symb_state = update_symb_state_after_folding symb_state framed_heap framed_preds pf_discharges new_gamma in
		  			let new_symb_state', missing_pred_args, existentials' = 
						process_missing_pred_assertion missing_pred_args subst (SS.union existentials new_existentials) new_symb_state framed_heap framed_preds pf_discharges new_gamma in 
					fold_predicate predicates pred_name pred_defs new_symb_state' params missing_pred_args new_spec_vars (Some existentials') search_info

		  		| _ -> None)))) in









let unify_symb_states_fold 
			(pred_name            : string)
			(existentials         : SS.t) 
			(pat_unification_plan  : jsil_logic_assertion list) 
			(pat_symb_state       : symbolic_state) 
			(symb_state           : symbolic_state) : symbolic_state_frame * SS.t * ((string * (jsil_logic_expr list)) option)  =
	
	let heap,     store,     pfs,     gamma,     preds     = symb_state in
	let pat_heap, pat_store, pat_pfs, pat_gamma, pat_preds = pat_symb_state in
	let pat_lvars = (ss_lvars pat_symb_state) in 

	print_debug (Printf.sprintf "STARTING: unify_symb_states_fold with UP: %s.\n" 
		(Symbolic_State_Print.string_of_unification_plan pat_unification_plan)); 

	(* 1. Init the substitution          *)
	let pat_subst  = init_substitution [] in

	(* 2. Unify stores                   *)
	(*  2.1 - find the pvars that are mapped to expressions containing existentials                            *)
	(*  2.2 - unify the stores except for the pvars that are mapped to lexprs containing existentials          *)
	(*  let filtered_pvars  = { x : x \in dom(store) /\ ((lvars (store(x)) \cap existentials) \neq \emptyset } *)
	(*  let unfiltered_vars = \dom(store) \ filtered_vars                                                      *)
	(*  let store' = store|_{unfiltered_vars}                                                                  *)
	(*  let pat_store' = pat_store|_{unfiltered_vars}                                                          *)
	(*  let discharges = { (le_pat, le) | x \in filtered_vars /\ le = store(x) /\ le_pat = pat_store(x)        *)
	(*  let discharges' = unify_stores (pfs, gamma, pat_subst, new_store, new_pat_store)	                   *)
	let unfiltered_vars, filtered_vars = SStore.partition store 
		(fun le -> SS.is_empty (SS.inter (get_lexpr_lvars le) existentials)) in  					
	let store'      = SStore.projection store     unfiltered_vars in
	let pat_store'  = SStore.projection pat_store unfiltered_vars in
	let discharges  = List.map 
		(fun x -> 
			match SStore.get pat_store x, SStore.get store x with 
			| Some le_pat_x, Some le_x -> (le_pat_x, le_x)
			| _, _ -> raise (UnificationFailure "")) filtered_vars in 
	let discharges' = (unify_stores pfs gamma pat_subst pat_store' store') in 
	print_debug (Printf.sprintf "unify_stores - done. pat_subst: %s\ndischarges: %s\n"
		(JSIL_Print.string_of_substitution pat_subst)
		(Symbolic_State_Print.string_of_discharges (discharges @ discharges')));

	(* 3. Find type information for the existentials using the pat_symb_state and extend the current  gamma  
	      with that additional information                                                                     *)
	(*  Find gamma_existentials st                                                                             *)
	(*   dom(gamma_existentials) \subseteq existentials                                                        *)
	(*   forall x \in filtered_vars :                                                                          *)
	(* 	   (pat_gamma |- pat_store(x) : tau) => (gamma + gamma_existentials |- store(x) : tau                  *)
	let gamma_existentials = TypEnv.init () in
	List.iter
		(fun x ->
			match SStore.get store x, TypEnv.get pat_gamma x with
			| Some le_x, Some x_type -> let _ = JSIL_Logic_Utils.infer_types_to_gamma false gamma gamma_existentials le_x x_type in ()
			|	_, _ -> ())
		filtered_vars;
	let gamma_existentials = TypEnv.filter_vars gamma_existentials existentials in	
	TypEnv.extend gamma_existentials gamma;
	let gamma = gamma_existentials in 
	
	(* 4. Initial frame for the search *)
	let initial_frame = pat_unification_plan, (heap, preds, (discharges @ discharges'), pat_subst), [], None in 

	(* 5. SEARCH *)
	let rec search 
			(frame_list : fold_extended_intermediate_frame list) : symbolic_state_frame * SS.t * ((string * (jsil_logic_expr list)) option) = 
		match frame_list with 
		| [] -> raise (UnificationFailure "")
		
		| (up, (heap_frame, preds_frame, discharges, pat_subst), pfs_to_check, missing_pred) :: rest_frame_list -> 	
			(match up with 
			| [] -> 
				(* A - All the spatial resources were successfully unified *)

				(* A.1 - Unify gammas *)
				if (not (unify_gammas pat_subst pat_gamma gamma)) then search rest_frame_list else (
					print_debug (Printf.sprintf "unify_gammas - done. pat_subst: %s\ndischarges: %s\nexistentials: %s\n"
						(JSIL_Print.string_of_substitution pat_subst)
						(Symbolic_State_Print.string_of_discharges (discharges @ discharges'))
						(String.concat ", " (SS.elements existentials)));

					(* A.2 - Unify pfs *)
					let complete_match_b, pfs_existentials, _, new_gamma, new_existentials = unify_pfs pat_subst (SS.elements existentials) pat_lvars pat_gamma pat_pfs gamma pfs discharges in 
					
					(* A.3 - Return *)
					if (complete_match_b) 
						then (heap_frame, preds_frame, pat_subst, pfs_existentials, new_gamma), (SS.union existentials new_existentials), missing_pred
						else search rest_frame_list
				)

			| LPointsTo _ :: rest_up
			| LEmptyFields _ :: rest_up 
			| LMetaData _ :: rest_up 
			| LExtensible _ :: rest_up -> 

				print_debug (Symbolic_State_Print.string_of_unification_step (List.hd up) pat_subst heap_frame preds_frame pfs gamma discharges); 
				
				(* B - Unify spatial assertion - no predicate assertion *)
				let new_frames : intermediate_frame list = unify_spatial_assertion pfs gamma pat_subst (List.hd up) heap_frame preds_frame in 
				let new_frames : fold_extended_intermediate_frame list = 
					List.map 
						(fun (h_f, p_f, new_discharges, pat_subst) -> rest_up, (h_f, p_f, (new_discharges @ discharges), pat_subst), pfs_to_check, missing_pred) 
						new_frames in 

				print_debug (Printf.sprintf "Unification result: %b" ((List.length new_frames) > 0));

				search (new_frames @ rest_frame_list)

			| LPred (p_name, largs) :: rest_up -> 

				print_debug (Symbolic_State_Print.string_of_unification_step (List.hd up) pat_subst heap_frame preds_frame pfs gamma discharges); 
				
				(* C - Unify pred assertion *)
				let new_frames : fold_extended_intermediate_frame list =
					List.map 
						(fun (p_f, pat_subst, new_discharges) -> rest_up, (SHeap.copy heap_frame, p_f, (new_discharges @ discharges), pat_subst), pfs_to_check, missing_pred) 
						(unify_pred_assertion pfs gamma pat_subst (LPred (p_name, largs)) preds_frame) in  

				print_debug (Printf.sprintf "Unification result: %b" ((List.length new_frames) > 0));

				if (((List.length new_frames) <> 0) || (p_name <> pred_name) || (missing_pred <> None))
					then (
						(* C.1 - the predicate was unified successfully or 
						   the predicate was not unified but it was not the one being folded - 
						   we continue the search *)
						search (new_frames @ rest_frame_list)
					) else (
						print_debug "Predicate Assertion NOT FOUND. PAS DE PROBLEME ON CONTINUE\n"; 

						(* C.2 - the predicate is the one we are looking for but we could NOT unify it  *)
						search ((rest_up, (heap_frame, preds_frame, discharges, pat_subst), pfs_to_check, (Some (p_name, largs))) :: rest_frame_list)
					)

			| LTypes type_asrts :: rest_up ->

				print_debug (Symbolic_State_Print.string_of_unification_step (List.hd up) pat_subst heap_frame preds_frame pfs gamma discharges); 

				let local_gamma = TypEnv.init () in
				List.iter (fun (x, typ) -> let x = match x with | LVar x -> x in TypEnv.update local_gamma x (Some typ)) type_asrts;
				if not (unify_gammas pat_subst local_gamma gamma) then (
					print_debug (Printf.sprintf "Failed type assertion %s; moving to next frame" (Symbolic_State_Print.string_of_unification_step (List.hd up) pat_subst heap_frame preds_frame pfs gamma discharges));
					search rest_frame_list 
				)
				else 
					let new_frame = rest_up, (heap_frame, preds_frame, discharges, pat_subst), pfs_to_check, missing_pred in
					search (new_frame::rest_frame_list) 

			| LEmp :: _
			| LStar _ :: _ -> 
				let asrt_str = JSIL_Print.string_of_logic_assertion (List.hd up) in
					raise (Failure (Printf.sprintf "DEATH: Unknown assertion in unification plan (%s)." asrt_str))
	
			(* PURE FORMULAE *)
			| pf :: rest_up -> (* PURE FORMULAE *)

				print_debug (Symbolic_State_Print.string_of_unification_step (List.hd up) pat_subst heap_frame preds_frame pfs gamma discharges); 

				(match pf with 
				(* We know le1, learning le2 *)
				| LEq (le1, le2) -> 
					let sle1 = lexpr_substitution pat_subst true le1 in 
					let more_pfs = Simplifications.subst_for_unification_plan ?gamma:(Some pat_gamma) le2 sle1 pat_subst in  
					(match more_pfs with 
					| None -> search rest_frame_list 
					| Some more_pfs -> 
						let pfs_to_check = pfs_to_check @ more_pfs in 
						print_debug_petar ("New pat subst:\n" ^ (JSIL_Print.string_of_substitution pat_subst));
						Hashtbl.iter (fun v le -> Hashtbl.replace pat_subst v (lexpr_substitution pat_subst true le) ) pat_subst;
						let new_frame = rest_up, (heap_frame, preds_frame, discharges, pat_subst), pfs_to_check, missing_pred in 
						search (new_frame :: rest_frame_list))
				| _ -> 
					let existentials = get_asrt_lvars pf in 
					let existentials = SS.diff existentials (substitution_domain pat_subst) in 
					(* Substitute in formula *)
					let pf_sbst = asrt_substitution pat_subst true pf in 
					(* Check if the current pfs entail the obtained substituted pf *)
					let pf_entailed : bool = Pure_Entailment.check_entailment existentials (PFS.to_list pfs) [ pf_sbst ] gamma in 
					(match pf_entailed with 
					| false -> 
						let new_frame = rest_up, (heap_frame, preds_frame, discharges, pat_subst), (pf :: pfs_to_check), missing_pred in
							search (new_frame :: rest_frame_list) 
					| true -> 
						let new_frame = rest_up, (heap_frame, preds_frame, discharges, pat_subst), pfs_to_check, missing_pred in
							search (new_frame :: rest_frame_list)))
			) in
			
	let start_time = Sys.time() in
	let result = search [ initial_frame ] in
	let end_time = Sys.time() in
	update_statistics "unify_ss_fold : search" (end_time -. start_time);
	result