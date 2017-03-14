open JSIL_Syntax
open Symbolic_State
open JSIL_Logic_Utils
open Symbolic_State_Basics
open Structural_Entailment




let bi_unify_stores (pat_store : symbolic_store) (store : symbolic_store) (pat_subst : substitution) (subst: substitution option) (pfs : jsil_logic_assertion list) (* solver *) (gamma : typing_environment) : ((jsil_logic_expr * jsil_logic_expr) list) option  =
	let start_time = Sys.time () in
	try
	print_debug (Printf.sprintf "Unifying stores:\nStore: %s \nPat_store: %s" (JSIL_Memory_Print.string_of_shallow_symb_store store false) (JSIL_Memory_Print.string_of_shallow_symb_store pat_store false)); 
	let discharges =
		Hashtbl.fold
			(fun var pat_lexpr discharges ->
				let lexpr = try Hashtbl.find store var with _ -> raise (Failure "the stores are not unifiable") in
				let rec spin_me_round pat_lexpr lexpr discharges =
				(*Printf.printf "(%s, %s)\n" (JSIL_Print.string_of_logic_expression pat_lexpr false) (JSIL_Print.string_of_logic_expression lexpr false);*)
				(match pat_lexpr, lexpr with

				| LLit pat_lit, LLit lit ->
					if (lit = pat_lit)
						then discharges
						else raise (Failure "Other literals: the stores are not unifiable")

				| ALoc pat_aloc, ALoc aloc ->
					extend_subst pat_subst pat_aloc (ALoc aloc);
					discharges

				| ALoc pat_aloc, (LLit (Loc loc)) ->
					extend_subst pat_subst pat_aloc (LLit (Loc loc));
					discharges

				| LVar lvar, _ ->
					if (Hashtbl.mem pat_subst lvar)
						then (let current = Hashtbl.find pat_subst lvar in
							if Pure_Entailment.is_equal current lexpr (DynArray.of_list pfs) (* solver *) gamma
								then discharges
								else raise (Failure "No no no no NO."))
						else (extend_subst pat_subst lvar lexpr;
								discharges)

				| ALoc pat_aloc, LVar lvar ->
					print_debug (Printf.sprintf "So, in unify_stores: Aloc %s, Lvar %s\n" pat_aloc lvar); 
					let loc = resolve_location lvar pfs in
					(match loc with
					| Some loc ->
						(* Printf.printf "I managed to resolve location and I know that %s = %s\n" lvar (JSIL_Print.string_of_logic_expression loc false);  *)
						extend_subst pat_subst pat_aloc loc; discharges
					| None     ->
						(match subst with
						| None -> 
							let new_aloc = fresh_aloc () in 
							extend_subst pat_subst pat_aloc (ALoc new_aloc);
							discharges
							
						| Some subst ->
							(* Printf.printf "I could not resolve the location and I am creating a new location\n"; *)
							let new_aloc = fresh_aloc () in
							extend_subst subst lvar (ALoc new_aloc);
							extend_subst pat_subst pat_aloc (ALoc new_aloc);
							discharges))

				| LLit lit, LVar lvar ->
					(match subst with
					| Some subst ->
						extend_subst subst lvar (LLit lit);
						discharges
					| None ->
						if (Pure_Entailment.old_check_entailment [] pfs [ (LEq (LVar lvar, LLit lit)) ] gamma)
							then discharges
							else raise (Failure (Printf.sprintf "LLit %s, LVar %s : the pattern store is not normalized." (JSIL_Print.string_of_literal lit false) lvar)))

				| LEList el1, LEList el2 ->
					(* Printf.printf ("Two lists of lengths: %d %d") (List.length el1) (List.length el2); *)
					if (List.length el1 = List.length el2) then
					begin
						(List.fold_left2
						(fun ac x y ->
							let new_ones = spin_me_round x y [] in
							new_ones @ ac)
						[] el1 el2) @ discharges
					end
					else
					begin
						[ (LLit (Bool true), LLit (Bool false)) ]
					end

				| le_pat, le -> if (le_pat = le) then discharges
				                                 else ((le_pat, le) :: discharges)) in
				spin_me_round pat_lexpr lexpr discharges)
			pat_store
			[] in
	let end_time = Sys.time () in
	JSIL_Syntax.update_statistics "unify_stores" (end_time -. start_time);
	Some discharges
	with (Failure msg) -> 
		let end_time = Sys.time () in
		JSIL_Syntax.update_statistics "unify_stores" (end_time -. start_time); None
		
		
		
	

(** 
	Unify two logical field-value lists

	@param pat_fv_list      Field-value list in the pattern heap
	@param fv_list          Field-value list in the current heap
	@param def_val   	      Default value of the object corresponding to fv_list
	@param p_formulae       Pure formulae of the current heap 
	@param gamma            Typing environment of the current heap
	@param subst            Substitution mapping the pattern symb_state to the current symb_state
		
	
*)
let unify_symb_fv_lists (pat_fv_list : symbolic_field_value_list)
												(fv_list     : symbolic_field_value_list)
												(def_val     : jsil_logic_expr) 
												(p_formulae  : pure_formulae)
												(gamma       : typing_environment) 
												(subst       : substitution) 
													: (symbolic_field_value_list * symbolic_field_value_list * symbolic_field_value_list * symbolic_discharge_list) option =

	(* Printf.printf "Inside unify_symb_fv_lists.\npat_fv_list: \n%s.\nfv_list: \n%s.\n" (JSIL_Memory_Print.string_of_symb_fv_list pat_fv_list false) (JSIL_Memory_Print.string_of_symb_fv_list fv_list false); *)

	let rec loop (fv_list : symbolic_field_value_list) (pat_list : symbolic_field_value_list) (matched_fv_list : symbolic_field_value_list) (anti_frame: symbolic_field_value_list) (discharges : symbolic_discharge_list) =
		match pat_list with
		| [] -> Some (fv_list, matched_fv_list, anti_frame, discharges)
		| (pat_field, pat_val) :: rest_pat_list ->
			let pf_equal, pf_different, res = unify_fv_pair (pat_field, pat_val) fv_list p_formulae gamma subst in
			
			(match pf_equal, pf_different, res with
			| true,  true,  _    -> raise (Failure "Death: bi_unify_symb_fv_lists")
			| true,  false, None -> None
			| false, _,  None ->
				print_debug (Printf.sprintf "I could NOT unify an fv-pair. pat_val: %s. def_val: %s" (JSIL_Print.string_of_logic_expression pat_val false) (JSIL_Print.string_of_logic_expression def_val false));
				(match def_val with
				| LUnknown -> 
					if (pf_different) 
						then loop fv_list rest_pat_list matched_fv_list ((pat_field, pat_val) :: anti_frame) discharges
						else None
				| _ ->
					let (bv, unifier) = unify_lexprs pat_val def_val p_formulae gamma subst in
					if (bv && (Symbolic_State_Functions.update_subst1 subst unifier))
						then (
							if (pf_different) 
								then loop fv_list rest_pat_list matched_fv_list anti_frame discharges
								else (
									let new_discharges = List.map (fun (field, _) -> (field, pat_field)) fv_list in 
									loop fv_list rest_pat_list matched_fv_list anti_frame (new_discharges @ discharges)			
						)) else None)
			| _, _, Some (rest_fv_list, matched_fv_pair) ->
				loop rest_fv_list rest_pat_list (matched_fv_pair :: matched_fv_list) anti_frame discharges) in
	let order_pat_list = order_fv_list pat_fv_list in
	loop fv_list order_pat_list [] [] []
	
	
	

let bi_unify_symb_heaps (pat_heap : symbolic_heap) (heap : symbolic_heap) pure_formulae gamma (subst : substitution) : (symbolic_heap * symbolic_heap * (jsil_logic_assertion list) * symbolic_discharge_list) option =
	print_debug (Printf.sprintf "Unify heaps %s \nand %s \nwith substitution: %s\nwith pure formulae: %s\nwith gamma: %s"
		(JSIL_Memory_Print.string_of_shallow_symb_heap pat_heap false)
		(JSIL_Memory_Print.string_of_shallow_symb_heap heap false)
		(JSIL_Memory_Print.string_of_substitution subst)
		(JSIL_Memory_Print.string_of_shallow_p_formulae pure_formulae false)
		(JSIL_Memory_Print.string_of_gamma gamma));
		
	let start_time = Sys.time () in
	let quotient_heap = create_empty_abs_heap () in
	let antiframe_heap = create_empty_abs_heap () in
	let pat_heap_domain : string list = get_heap_domain pat_heap subst in
	print_debug (Printf.sprintf "PatHeapDomain: %s" (String.concat ", " pat_heap_domain));
	
	let just_pick_the_first locs = 
		match locs with 
		| [] -> print_debug "DEATH. just_pick_the_first\n"; None
		| loc :: rest -> Some (loc, rest) in 
	
	
	let rec pick_loc_that_exists_in_both_heaps locs traversed_locs  = 
		match locs with 
		| [] -> just_pick_the_first traversed_locs
		| loc :: rest -> 
			if (LHeap.mem heap loc) 
				then Some (loc, (traversed_locs @ rest))
				else pick_loc_that_exists_in_both_heaps rest (traversed_locs @ [ loc ]) in 
	
	let pick_pat_loc (locs_to_visit : string list) subst : (string * (string list)) option = 
		print_debug "pick_pat_loc\n";
		
		let rec loop (remaining_locs : string list) (traversed_locs : string list) : (string * (string list)) option = 
			match remaining_locs with 
			| [] -> pick_loc_that_exists_in_both_heaps traversed_locs []
			| loc :: rest -> 
				if ((not (is_abs_loc_name loc)) || (Hashtbl.mem subst loc)) 
					then Some (loc, (traversed_locs @ rest)) 
					else loop rest (traversed_locs @ [ loc ]) in 
		loop locs_to_visit [] in 	
		
	try
		(* let pfs : jsil_logic_assertion list =
			List.fold_left
				(fun pfs pat_loc -> *)
					
		let rec loop locs_to_visit pfs discharges = 
			(match locs_to_visit with 
			| [] -> (pfs, discharges)
			| _ ->  
				(match pick_pat_loc locs_to_visit subst with  
				| Some (pat_loc, rest_locs) -> 
					print_debug (Printf.sprintf "Location: %s" pat_loc);
					print_debug (Printf.sprintf "Substitution: %s" (JSIL_Memory_Print.string_of_substitution subst));
					(match abs_heap_get pat_heap pat_loc with
					| Some (pat_fv_list, pat_def) ->
			  		(if ((pat_def <> LNone) && (pat_def <> LUnknown)) then raise (Failure "Illegal Default Value")  else (
							let loc = try
								let le = Hashtbl.find subst pat_loc in
								(match le with
								| LLit (Loc loc) -> loc
								| ALoc loc -> loc
								| LVar v -> 
									let loc = find_me_Im_a_loc (pfs_to_list pure_formulae) le in 
									(match loc with 
									| Some loc -> loc
									| None -> raise (Failure "I cannot unify this"))
				  			| _ ->
									(* I really think this case is wrong!!!*)
									pat_loc)
								with _ -> (* this case is very interesting *) pat_loc in
							let fv_list, (def : jsil_logic_expr) =
								(match abs_heap_get heap loc with 
								| Some (fv_list, def) -> fv_list, def 
								| None -> 
									let msg = Printf.sprintf "Location %s in pattern has not been matched" loc in
									Printf.printf "%s\n" msg;
									raise (Failure msg)) in
							let fv_lists = unify_symb_fv_lists pat_fv_list fv_list def pure_formulae gamma subst in
							(match fv_lists with
							| Some (frame_fv_list, matched_fv_list, antiframe_fv_list, new_discharges) when ((pat_def = LNone) && ((List.length frame_fv_list) > 0)) ->
								print_debug (Printf.sprintf "fv_lists unified successfully");
								print_debug (Printf.sprintf "QH:%s\nAFH:%s" 
									(JSIL_Memory_Print.string_of_shallow_symb_heap quotient_heap false)
									(JSIL_Memory_Print.string_of_shallow_symb_heap antiframe_heap false));
								let all_fields_in_new_fv_list_are_none =
									List.fold_left (fun ac (_, field_val) -> if (not ac) then ac else (field_val = LNone)) true frame_fv_list in
								if all_fields_in_new_fv_list_are_none then (
									abs_heap_put quotient_heap  loc []                def; 
									abs_heap_put antiframe_heap loc antiframe_fv_list def; 
									loop rest_locs pfs (new_discharges @ discharges))
								else raise (Failure "LNone in precondition")
							| Some (frame_fv_list, matched_fv_list, antiframe_fv_list, new_discharges) ->
								abs_heap_put quotient_heap  loc frame_fv_list     def;
								abs_heap_put antiframe_heap loc antiframe_fv_list def;
								print_debug (Printf.sprintf "Adding sth to QH and AF.");
								print_debug (Printf.sprintf "QH:%s\nAFH:%s" 
									(JSIL_Memory_Print.string_of_shallow_symb_heap quotient_heap false)
									(JSIL_Memory_Print.string_of_shallow_symb_heap antiframe_heap false));
								let new_pfs : jsil_logic_assertion list = make_all_different_pure_assertion frame_fv_list matched_fv_list in
								loop rest_locs (new_pfs @ pfs) (new_discharges @ discharges)
							| None -> print_debug "fv_lists not unifiable!"; raise (Failure ("fv_lists not unifiable")))))
						| _ -> raise (Failure ("Pattern heaps cannot have default values")))
				| None -> raise (Failure ("Pattern heaps cannot have default values")))) in 
			
		let (pfs : (jsil_logic_assertion list)), (discharges: (symbolic_discharge_list)) = loop pat_heap_domain [] [] in 
				
		print_debug (Printf.sprintf "Heap again %s" (JSIL_Memory_Print.string_of_shallow_symb_heap heap false));
		
		heap_iterator 
			heap
			(fun loc (fv_list, def) ->
				match abs_heap_get quotient_heap loc with 
				| Some _ -> () 
				| None   -> abs_heap_put quotient_heap loc fv_list def);
		
		heap_iterator
			quotient_heap
			(fun loc (fv_list, def) -> 
				match def with 
				| LUnknown -> 
					if ((List.length fv_list) = 0)
						then abs_heap_remove quotient_heap loc
				| _ -> ()); 
		
		heap_iterator 
			antiframe_heap
			(fun loc (fv_list, def) -> 
				match def with 
				| LUnknown -> 
					if ((List.length fv_list) = 0)
						then abs_heap_remove antiframe_heap loc
				| _ -> ()); 
		
		let end_time = Sys.time () in
		JSIL_Syntax.update_statistics "unify_symb_heaps" (end_time -. start_time);
		print_debug (Printf.sprintf "End of unify_symb_heaps: do enjoy the quotient_heap: %s" (JSIL_Memory_Print.string_of_shallow_symb_heap quotient_heap false));
		Some (quotient_heap, antiframe_heap, pfs, discharges)
	with (Failure msg) ->
		let end_time = Sys.time () in
		JSIL_Syntax.update_statistics "unify_symb_heaps" (end_time -. start_time);
		None
	




let bi_unify_symb_states lvars pat_symb_state (symb_state : symbolic_state) : 
	(bool * symbolic_heap * symbolic_heap * predicate_set * substitution * (jsil_logic_assertion list) * typing_environment) option  =

	print_debug (Printf.sprintf "LVARS: %s" (String.concat ", " lvars));

	let start_time = Sys.time () in

	let heap_0, store_0, pf_0, gamma_0, preds_0 (*, solver *) = symb_state in
	let heap_1, store_1, pf_1, gamma_1, preds_1 (*, _  *) = copy_symb_state pat_symb_state in

	(* STEP 0 - Unify stores, heaps, and predicate sets                                                                                                  *)
	(* subst = empty substitution                                                                                                                        *)
	(* discharges_0 = unify_stores (store_1, store_0, subst, pi_0, gamma_0)	                                                                             *)
	(* discharges_1, heap_f, new_pfs = unify_heaps (heap_1, heap_0, subst, pi_0)                                                                         *)
	(* discharges_2, preds_f = unify_predicate_sets (preds_1, preds_0, subst, pi_0)                                                                      *)
	(* if discharges_i != None for i \in {0, 1, 2} => return Some ((disharches_0 @ discharges_1 @ discharges_2), subst, heap_f, preds_f, new_pfs)        *)
	(* if exists i \in {0, 1, 2} . discharges_i = None => return None                                                                                    *)
	(* If Step 0 returns a list of discharges and a substitution then the following implication holds:                                                   *)
	(*    pi_0 |- discharges  => store_0 =_{pi_0} subst(store_1)  /\ heap_0 =_{pi_0} subst(heap_1) + heap_f /\ preds_0 =_{pi_0} subst(preds_1) + preds_f *)
	let step_0 () =
		let start_time = Sys.time() in
		let subst = init_substitution [] in
		let discharges_0 = bi_unify_stores store_1 store_0 subst None (pfs_to_list pf_0) (* solver *) gamma_0 in
		let result = (match discharges_0 with
		| Some discharges_0 ->
			print_debug (Printf.sprintf "Discharges: %d\n" (List.length discharges_0));
			List.iter (fun (x, y) -> print_debug (Printf.sprintf "\t%s : %s\n" (JSIL_Print.string_of_logic_expression x false) (JSIL_Print.string_of_logic_expression y false))) discharges_0;
			let ret_1 = bi_unify_symb_heaps heap_1 heap_0 pf_0 gamma_0 subst in
			(match ret_1 with
			| Some (heap_f, anti_frame, new_pfs, negative_discharges) ->
				print_debug (Printf.sprintf "Heaps unified successfully.\n");
				let ret_2 = unify_pred_arrays preds_1 preds_0 pf_0 gamma_0 subst in
				(match ret_2 with
				| Some (subst, preds_f, []) ->
					let spec_vars_check = spec_logic_vars_discharge subst lvars pf_0 gamma_0 in
	  				if (spec_vars_check)
							then Some (discharges_0, subst, heap_f, anti_frame, preds_f, new_pfs)
							else (Printf.printf "Failed spec vars check\n"; None) 
				| Some (_, _, _) | None -> ( print_debug (Printf.sprintf "Failed to unify predicates\n"); None))
			| None -> ( print_debug (Printf.sprintf "Failed to unify heaps\n"); None))
		| None -> ( print_debug (Printf.sprintf "Failed to unify stores\n"); None)) in
		let end_time = Sys.time() in
		JSIL_Syntax.update_statistics "USS: Step 0" (end_time -. start_time);
		result in

	(* STEP 1 - Pure entailment and gamma unification                                                                                                    *)
	(* existentials = vars(Sigma_pat) \ dom(subst)                                                                                                       *)
	(* subst' = subst + [ x_i \in existentials -> fresh_lvar() ]                                                                                         *)
	(* gamma_0' = gamma_0 + gamma_existentials, where gamma_existentials(x) = gamma_1(y) iff x = subst'(y)                                               *)
	(* unify_gamma(gamma_1, gamma_0', store_1, subst, existentials) = true                                                                               *)
	(* pf_0 + new_pfs |-_{gamma_0'} Exists_{existentials} subst'(pf_1) + pf_list_of_discharges(discharges)                                               *)
	let step_1 discharges subst new_pfs =
		let start_time = Sys.time() in
		let existentials = get_subtraction_vars (get_symb_state_vars_as_list false pat_symb_state) subst in
		let fresh_names_for_existentials = (List.map (fun v -> fresh_lvar ()) existentials) in
		let subst_existentials = init_substitution2 existentials (List.map (fun v -> LVar v) fresh_names_for_existentials) in
		extend_substitution subst existentials (List.map (fun v -> LVar v) fresh_names_for_existentials);
		let gamma_0' =
			if ((List.length existentials) > 0)
				then (
					let gamma_0' = copy_gamma gamma_0 in
					let gamma_1_existentials = filter_gamma_with_subst gamma_1 existentials subst_existentials in
					extend_gamma gamma_0' gamma_1_existentials;
					gamma_0')
				else gamma_0 in

		let unify_gamma_check = (unify_gamma gamma_1 gamma_0' store_1 subst existentials) in
		let result = if (unify_gamma_check) then
		begin
			merge_pfs pf_0 (DynArray.of_list new_pfs);
		  let pf_1_subst_list = List.map (fun a -> assertion_substitution a subst true) (pfs_to_list pf_1) in
			let pf_discharges = pf_list_of_discharges discharges subst false in
			let pfs = pf_1_subst_list @ pf_discharges in

			print_debug (Printf.sprintf "Checking if %s\n entails %s\n with existentials\n%s\nand gamma %s"
				(JSIL_Memory_Print.string_of_shallow_p_formulae pf_0 false)
				(JSIL_Memory_Print.string_of_shallow_p_formulae (DynArray.of_list pfs) false)
				(List.fold_left (fun ac x -> ac ^ " " ^ x) "" fresh_names_for_existentials)
				(JSIL_Memory_Print.string_of_gamma gamma_0'));

			let entailment_check_ret = Pure_Entailment.old_check_entailment fresh_names_for_existentials (pfs_to_list pf_0) pfs gamma_0' in
			print_debug (Printf.sprintf "unify_gamma_check: %b. entailment_check: %b" unify_gamma_check entailment_check_ret);
			Some (entailment_check_ret, pf_discharges, pf_1_subst_list, gamma_0')
		end else (print_debug "Gammas not unifiable."; None) in
		let end_time = Sys.time() in
		JSIL_Syntax.update_statistics "USS: Step 1" (end_time -. start_time);
		result in

	(* Actually doing it!!! *)
	let result = (match step_0 () with
	| Some (discharges, subst, heap_f, anti_frame, preds_f, new_pfs) ->
		(match (step_1 discharges subst new_pfs) with
		| Some (entailment_check_ret, pf_discharges, pf_1_subst_list, gamma_0') -> 
				Some (entailment_check_ret, heap_f, anti_frame, preds_f, subst, (pf_1_subst_list @ pf_discharges), gamma_0')
		| None -> None)
	| None -> None) in
	let end_time = Sys.time () in
		JSIL_Syntax.update_statistics "unify_symb_states" (end_time -. start_time);
		result
	


(** 
  Extends symb_state with the pure part of pat_symb_state 
	symb_state and pat_symb_state are connected via subst
*)
let enrich_pure_part (symb_state : symbolic_state)
										 (pat_symb_state : symbolic_state) 
										 (subst : substitution) : symbolic_state =
	
	let pat_gamma = (get_gamma pat_symb_state) in
	let pat_pfs = (get_pf pat_symb_state) in
	let pat_gamma = copy_gamma pat_gamma in
	let pat_pfs = copy_p_formulae pat_pfs in
	
	let pfs = pf_substitution pat_pfs subst false in
	let gamma = gamma_substitution pat_gamma subst false in
	merge_gammas gamma (get_gamma symb_state);
	merge_pfs pfs (get_pf symb_state);
	let store =	get_store symb_state in
	let heap = get_heap symb_state in
	let preds = get_preds symb_state in
	let new_symb_state = (heap, store, pfs, gamma, preds) in
	new_symb_state 


	
let bi_unify_symb_state_against_post 
		(proc_name     : string)
		(spec          : jsil_n_single_spec)
		(symb_state    : symbolic_state) 
		(anti_frame    : symbolic_state)
		(flag          : jsil_return_flag)
		(symb_exe_info : symbolic_execution_search_info) =
	let print_error_to_console msg =
		(if (msg = "")
			then Printf.printf "Failed to verify a spec of proc %s\n" proc_name
			else Printf.printf "Failed to verify a spec of proc %s -- %s\n" proc_name msg);
		let final_symb_state_str = JSIL_Memory_Print.string_of_shallow_symb_state symb_state in
		let post_symb_state_str = JSIL_Memory_Print.string_of_symb_state_list spec.n_post in
		Printf.printf "Final symbolic state: %s\n" final_symb_state_str;
		Printf.printf "Post condition: %s\n" post_symb_state_str in
	
	let enrich_symb_state_with_heap symb_state new_heap subst = 
		let old_heap, store, pfs, gamma, preds = symb_state in 
		let new_heap' = heap_substitution new_heap subst false in
		Symbolic_State_Functions.merge_heaps old_heap new_heap' pfs gamma in 

	let rec loop 
				(posts : symbolic_state list) 
				(computed_posts : (symbolic_state * symbolic_state) list) 
						: (symbolic_state * symbolic_state) list =
		(match posts with
		| [] -> 
			if ((List.length computed_posts) > 0)
				then computed_posts 
				else (
					print_error_to_console "Non_unifiable symbolic states";  
				raise (Failure "post condition is not unifiable"))
		| post :: rest_posts ->
			let subst = bi_unify_symb_states spec.n_lvars post symb_state in
			(match subst with
			| Some (true, _, heap_af, _, subst, _, _) ->
				(* complete match with the post *)
				let symb_state = copy_symb_state symb_state in 
				enrich_symb_state_with_heap symb_state heap_af subst;
				enrich_symb_state_with_heap anti_frame heap_af subst;  
				[ (symb_state, anti_frame) ]
				
			| Some (false, _, heap_af, _, subst, _, _) ->	
				let symb_state = copy_symb_state symb_state in 
				enrich_symb_state_with_heap symb_state heap_af subst; 
				enrich_symb_state_with_heap anti_frame heap_af subst; 
				let new_symb_state : symbolic_state = enrich_pure_part symb_state post subst in 
				let new_anti_frame : symbolic_state = enrich_pure_part anti_frame post subst in 
				loop rest_posts ((new_symb_state, new_anti_frame) :: computed_posts)
					
			| _  -> loop rest_posts computed_posts)) in
		 	
	let processed_posts = loop spec.n_post [] in  
	match processed_posts with 
	| []     -> raise (Failure "Specification not verifiable")
	| _ :: _ -> processed_posts
