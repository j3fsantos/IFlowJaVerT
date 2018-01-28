open CCommon
open JSIL_Syntax
open Symbolic_State
open JSIL_Logic_Utils

exception SymbExecFailure of string

(*************************************)
(** Symbolic Heap Functions         **)
(*************************************)

(**
  find_field (pfs, gamma, fv_list, loc, field) = fv_list', (field', val)
	   st:
		    fv_list = fv_list' U (field', val)
				and
				pfs |=_{gamma} field = field' 
*)
let find_field
		(pfs : pure_formulae) (gamma : typing_environment)
		(fv_list : symbolic_field_value_list)
		(loc : string) (field : jsil_logic_expr) : (symbolic_field_value_list * (jsil_logic_expr * (permission * jsil_logic_expr))) option  =
	
	let rec find_field_rec fv_list traversed_fv_list =
		match fv_list with
		| [] -> None
		| (field', (perm, value)) :: rest ->
			(if (Pure_Entailment.is_equal field' field pfs gamma)
				then Some (traversed_fv_list @ rest, (field', (perm, value)))
				else find_field_rec rest ((field', (perm, value)) :: traversed_fv_list)) in
	find_field_rec fv_list []


let sheap_put 
			(pfs : pure_formulae) (gamma : typing_environment)
			(heap : symbolic_heap) (loc : string) (field : jsil_logic_expr) (perm : permission) (value : jsil_logic_expr) : unit =
	
	let (fv_list, domain), metadata, ext = heap_get_unsafe heap loc in
	(match (find_field pfs gamma fv_list loc field), domain with 
	| Some (framed_fv_list, _), _ -> heap_put heap loc ((field, (perm, value)) :: framed_fv_list) domain metadata ext
	| None, Some domain -> 
		let a_set_inclusion = LNot (LSetMem (field, domain)) in 
		if (Pure_Entailment.check_entailment SS.empty (pfs_to_list pfs) [ a_set_inclusion ] gamma) then (
			let new_domain = LSetUnion [ domain; LESet [ field ]] in 
			(* let new_domain = Normaliser.normalise_lexpr gamma new_domain in *)
			let new_domain = Simplifications.reduce_expression_no_store gamma pfs new_domain in
			heap_put heap loc ((field, (perm, value)) :: fv_list) (Some new_domain) metadata ext
		) else (
			let msg = Printf.sprintf "sheap_put. loc: %s. field: %s. value: %s. fv_list:\n%s\n"  
				loc (JSIL_Print.string_of_logic_expression field) (JSIL_Print.string_of_logic_expression value)
				(Symbolic_State_Print.string_of_fv_list fv_list) in 
			raise (SymbExecFailure msg)
		)
	| _ -> 
		let msg = Printf.sprintf "sheap_put. loc: %s. field: %s. value: %s. fv_list:\n%s\n"  
				loc (JSIL_Print.string_of_logic_expression field) (JSIL_Print.string_of_logic_expression value)
				(Symbolic_State_Print.string_of_fv_list fv_list) in 
		raise (SymbExecFailure msg))


let sheap_get 
		(pfs : pure_formulae) (gamma : typing_environment)
		(heap : symbolic_heap) (loc : string) (field : jsil_logic_expr) : jsil_logic_expr = 

	let (fv_list, domain), _, _ = heap_get_unsafe heap loc in
	(match (find_field pfs gamma fv_list loc field), domain with 
	| Some (_, (_, (_, value))), _ -> value 
	| None, Some domain -> 
		let a_set_inclusion = LNot (LSetMem (field, domain)) in 
		if (Pure_Entailment.check_entailment SS.empty (pfs_to_list pfs) [ a_set_inclusion ] gamma) 
			then LNone
			else raise (SymbExecFailure "sheap_get")
	| _ -> raise (SymbExecFailure "sheap_get"))


let merge_domains 
		(pfs : pure_formulae) (gamma : typing_environment)
		(domain_l : jsil_logic_expr option) (domain_r : jsil_logic_expr option) : jsil_logic_expr option = 
	match domain_l, domain_r with 
	| None, None -> None
	| None, Some domain 
	| Some domain, None -> Some domain 
	| Some set1, Some set2 -> 
		let set = LSetUnion [ set1; set2 ] in
		(* let set = Normaliser.normalise_lexpr gamma set in *)  
		let set = Simplifications.reduce_expression_no_store gamma pfs set in
		Some set 


let merge_heaps 
			(pfs : pure_formulae) (gamma : typing_environment)
			(heap : symbolic_heap) (new_heap : symbolic_heap) : unit =
	
	print_debug_petar (Printf.sprintf "STARTING merge_heaps with heap:\n%s\npat_heap:\n%s\npfs:\n%s\ngamma:\n%s\n"
		(Symbolic_State_Print.string_of_symb_heap heap) (Symbolic_State_Print.string_of_symb_heap new_heap)
		(Symbolic_State_Print.string_of_pfs pfs) (Symbolic_State_Print.string_of_gamma gamma)
	);
	
	(* This is a bit strange, what if there are duplicates in the fv lists? Or contradictions with empty_fields and existing cells? TODO *)
	heap_iterator new_heap 
		(fun loc ((n_fv_list, n_domain), n_metadata, n_ext) ->
			match heap_get heap loc with 
			| Some ((fv_list, domain), metadata, ext) -> 
				(match (ext = n_ext) with
				| false -> raise (Failure "Heaps not mergeable. Extensibility mismatch.")
				| true -> match (Pure_Entailment.check_entailment SS.empty (pfs_to_list pfs) [ LEq (metadata, n_metadata) ] gamma) with
					| false -> raise (Failure "Heaps not mergeable. Metadata not provably equal.")  
					| true -> heap_put heap loc (n_fv_list @ fv_list) (merge_domains pfs gamma domain n_domain)) metadata ext
			| None -> 
				heap_put heap loc n_fv_list n_domain n_metadata n_ext); 

	(* Garbage collection - What happens here now?! TODO *)
	heap_iterator heap (fun loc ((fv_list, domain), _, _) ->
		(match fv_list, domain with
		| [], None -> heap_remove heap loc
		| _, _ -> ()));

	print_debug "Finished merging heaps."


let lexpr_is_none (pfs : pure_formulae) (gamma : typing_environment) (le : jsil_logic_expr) : bool option = 
	if (Pure_Entailment.is_equal le LNone pfs gamma) then Some true else (
		if (Pure_Entailment.is_different le LNone pfs gamma) 
			then Some false 
			else None)



(*************************************)
(** Predicate functions             **)
(*************************************)

let predicate_assertion_equality pred pat_pred pfs gamma (spec_vars : SS.t) (existentials : string list) =
	print_debug_petar (Printf.sprintf "Entering predicate_assertion_equality.\n");

	let subst = init_substitution [] in
	let extss = SS.of_list existentials in

	let rec unify_pred_args les pat_les =
		(match les, pat_les with
		| [], [] -> Some subst
		| le :: rest_les, pat_le :: rest_pat_les ->
			print_debug_petar (Printf.sprintf "I am going to test if %s CAN BE equal to %s\n" (JSIL_Print.string_of_logic_expression le) (JSIL_Print.string_of_logic_expression pat_le));
			let _, sbt = Simplifications.simplify_pfs_with_subst (DynArray.of_list [ LEq (pat_le, le) ]) gamma in
			(match sbt with
			| Some sbt ->
					(Hashtbl.iter (fun v le -> (match le with
					| LVar v' when ((SS.mem v' extss) && not (SS.mem v extss)) -> 
							Hashtbl.remove sbt v; Hashtbl.add sbt v' (LVar v)
					| _ -> ())) sbt); 
					Hashtbl.filter_map_inplace (fun v le -> if ((SS.mem v extss && not (Hashtbl.mem subst v))) then Some le else None) sbt;
					Hashtbl.iter (fun v le -> Hashtbl.add subst v le) sbt;
					let s_pfs = pfs_substitution subst true pfs in
					let s_le  = lexpr_substitution subst true le in
					let s_pat_le = lexpr_substitution subst true pat_le in
					print_debug_petar (Printf.sprintf "I am going to test if %s CAN BE equal to %s\n" (JSIL_Print.string_of_logic_expression s_le) (JSIL_Print.string_of_logic_expression s_pat_le));
					if (Pure_Entailment.is_equal s_le s_pat_le s_pfs gamma) 
						then unify_pred_args rest_les rest_pat_les
						else None
			| None -> None)) in

	match pred, pat_pred with
	| (name, les), (pat_name, pat_les) ->
		if (name = pat_name) then
			unify_pred_args les pat_les
		else None
	| _, _ -> raise (Failure "predicate_assertion_equality: FATAL ERROR")


let subtract_pred 
		(pred_name    : string)
		(args         : jsil_logic_expr list)
		(pred_set     : predicate_set)
		(pfs          : pure_formulae)
		(gamma        : typing_environment)
		(spec_vars    : SS.t)
		(existentials : string list) 
		(delete_pred  : bool) : substitution option =
	let pred_list = preds_to_list pred_set in
	let rec loop pred_list index =
		(match pred_list with
		| [] -> None
		| pred :: rest_pred_list ->
			(match (predicate_assertion_equality pred (pred_name, args) pfs gamma spec_vars existentials) with
			| None -> loop rest_pred_list (index + 1)
			| Some subst -> Some (index, subst))) in

	match loop pred_list 0 with 
	| None -> None 
	| Some (index, subst) -> 
		if(delete_pred) then DynArray.delete pred_set index; Some subst

	


(*************************************)
(** Symbolic State functions        **)
(*************************************)



let merge_symb_states
		(symb_state_l : symbolic_state)
		(symb_state_r : symbolic_state)
		(subst : substitution) : symbolic_state =
	(* Printf.printf "gamma_r: %s\n." (Symbolic_State_Print.string_of_gamma (get_gamma symb_state_r)); *)
	let aux_symb_state = (ss_copy symb_state_r) in
	let symb_state_r = ss_substitution subst false aux_symb_state in
	let heap_l, store_l, pf_l, gamma_l, preds_l = symb_state_l in
	let heap_r, store_r, pf_r, gamma_r, preds_r = symb_state_r in
	pfs_merge pf_l pf_r;
	merge_gammas gamma_l gamma_r;
	merge_heaps pf_l gamma_l heap_l heap_r;
	DynArray.append preds_r preds_l;
	print_debug ("Finished merge_symb_states");
	(heap_l, store_l, pf_l, gamma_l, preds_l)


(**
  * Check if the pfs of symb_state are compatible with those of pat_symb_state 
  * when they are connected via subst *)
let compatible_pfs 
	(symb_state     : symbolic_state) 
	(pat_symb_state : symbolic_state) 
	(subst          : substitution) : bool =
	
	let pfs = ss_pfs symb_state in
	let gamma = ss_gamma symb_state in
	let pat_pfs = ss_pfs pat_symb_state in
	let pat_gamma = ss_gamma pat_symb_state in
	
	let pat_pfs = pfs_substitution subst false pat_pfs in
	let pat_gamma = gamma_substitution pat_gamma subst false in
	let gamma = gamma_copy gamma in
	merge_gammas gamma pat_gamma;
	
	let pf_list = (pfs_to_list pat_pfs) @ (pfs_to_list pfs) in
	let is_sat = Pure_Entailment.check_satisfiability pf_list gamma in

	(if (not is_sat) then 
		print_debug (Printf.sprintf "These pfs are not compatible: %s"
			(String.concat "\n" (List.map (fun a -> JSIL_Print.string_of_logic_assertion a) pf_list)))
	); 

	is_sat 


let merge_symb_state_with_posts  
	(proc              : jsil_procedure)
	(spec              : jsil_n_single_spec) 
	(caller_symb_state : symbolic_state) 
	(symb_state_frame  : symbolic_state_frame) : (symbolic_state * jsil_return_flag * jsil_logic_expr) list = 

	let framed_heap, framed_preds, subst, pf_discharges, new_gamma = symb_state_frame in 
	let symb_state_frame = ss_replace_heap  caller_symb_state framed_heap in
	let symb_state_frame = ss_replace_preds symb_state_frame framed_preds in
	let symb_state_frame = ss_replace_gamma symb_state_frame new_gamma in
	
	let ret_flag = spec.n_ret_flag in
	let ret_var  = proc_get_ret_var proc ret_flag in

	print_debug_petar (Printf.sprintf "Procedure is: %s, return variable is: %s" proc.proc_name ret_var);

	let f_post (post : symbolic_state) : (symbolic_state * jsil_return_flag * jsil_logic_expr) list =
		let post_makes_sense = compatible_pfs symb_state_frame post subst in
		if (post_makes_sense) then (
			let new_symb_state = ss_copy symb_state_frame in
			let new_symb_state = merge_symb_states new_symb_state post subst in
			ss_extend_pfs new_symb_state (pfs_of_list pf_discharges);
			print_debug_petar (Printf.sprintf "Postcondition is: %s" (Symbolic_State_Print.string_of_symb_state post));
			let ret_lexpr = store_get_safe (ss_store post) ret_var in
			let ret_lexpr = (match ret_lexpr with
			| None -> print_debug_petar "Warning: Store return variable not present; implicitly empty"; LLit Empty
			| Some le -> let result = JSIL_Logic_Utils.lexpr_substitution subst false le in
			  print_debug_petar (Printf.sprintf "Found return value: %s" (JSIL_Print.string_of_logic_expression le));
				result) in
			[ (new_symb_state, ret_flag, ret_lexpr) ]
		) else [] in 

	List.concat (List.map f_post spec.n_post) 
			

let enrich_pure_part 
	(symb_state     : symbolic_state)
	(symb_state_pat : symbolic_state)
	(subst          : substitution) : bool * symbolic_state =
	
	let pre_gamma = gamma_copy (ss_gamma symb_state_pat)     in
	let pre_pfs   = pfs_copy (ss_pfs symb_state_pat)         in	
	let pfs       = pfs_substitution subst false pre_pfs     in
	let gamma     = gamma_substitution pre_gamma subst false in
	
	merge_gammas gamma (ss_gamma symb_state);
	pfs_merge pfs (ss_pfs symb_state);
	let store          = store_copy (ss_store symb_state) in
	let heap           = ss_heap symb_state               in
	let preds          = ss_preds symb_state              in
	let new_symb_state = (heap, store, pfs, gamma, preds) in
	
	let is_sat = Pure_Entailment.check_satisfiability (ss_pfs_list new_symb_state) (ss_gamma new_symb_state) in
	(is_sat, new_symb_state)



(*************************************)
(** Normalised Spec functions       **)
(*************************************)
let copy_single_spec s_spec =
	let copy_pre  = ss_copy s_spec.n_pre in
	let copy_post = List.map ss_copy s_spec.n_post in
	{
		n_pre              = copy_pre;
		n_post             = s_spec.n_post;
		n_ret_flag         = s_spec.n_ret_flag;
		n_lvars            = s_spec.n_lvars; 
		n_subst            = s_spec.n_subst; 
		n_unification_plan = s_spec.n_unification_plan
	}
	
(*************************************)
(** Garbage collection              **)
(*************************************)

let get_locs_symb_state symb_state =
	let heap, store, pfs, gamma, preds = symb_state in 
	let lheap  = heap_alocs  heap  in
	let lstore = store_alocs store in
	let lpfs   = pfs_alocs   pfs   in
	let lpreds = preds_alocs preds in
	SS.union lheap (SS.union lstore (SS.union lpfs lpreds))
	
let collect_garbage (symb_state : symbolic_state) = 
	let heap, store, pfs, gamma, preds = symb_state in
	let dangling_locations = 	Heap.fold
		(fun loc ((fv_list, default), _, _) locs ->
			match (is_abs_loc_name loc), default, fv_list with
			| true, None, [] 
			| true, Some (LESet []), [] -> SS.add loc locs
			| _ -> locs
  	)
		heap
		SS.empty in
	if (dangling_locations = SS.empty) then symb_state else (
	let ss_vars = get_locs_symb_state symb_state in
	let collectable_locs = SS.diff dangling_locations ss_vars in
	SS.iter (fun loc -> Heap.remove heap loc) collectable_locs;
		print_debug (Printf.sprintf "GCOL: Found locations: %s"
			(String.concat ", " (SS.elements ss_vars)));
		print_debug (Printf.sprintf "GCOL: Dangling locations: %s"
			(String.concat ", " (SS.elements dangling_locations)));
		print_debug (Printf.sprintf "GCOL: Collectable locations: %s"
			(String.concat ", " (SS.elements collectable_locs)));
	symb_state)

