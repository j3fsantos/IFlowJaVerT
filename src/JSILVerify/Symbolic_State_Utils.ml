open CCommon
open SCommon
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
	(pfs : pure_formulae) (gamma : TypEnv.t) (fv_list : SFVL.t) (name : jsil_logic_expr) : (jsil_logic_expr * (Permission.t * jsil_logic_expr)) option  =
	
	let oresult = SFVL.get fv_list name in
	Option.map_default (fun (result : SFVL.field_value) -> Some (name, (result.permission, result.value)))
	(
		let is_lit_name = (match name with | LLit _ -> true | _ -> false) in
		let result = ref None in
		let found = ref false in
		SFVL.iterator fv_list
		(fun name' value' ->
			let is_lit_name' = (match name' with | LLit _ -> true | _ -> false) in
			if (not !found && (not is_lit_name || not is_lit_name')) then
			(if (Pure_Entailment.is_equal name name' pfs gamma) then
				( found := true; result := Some (name', (value'.permission, value'.value)) )
			)
		);
		!result
	)
	oresult

(** I cannot get the following four into SHeap because of Pure_Entailment *)
let sheap_put 
	(pfs : pure_formulae) (gamma : TypEnv.t)
	(heap : SHeap.t) (loc : string) (field : jsil_logic_expr) (perm : Permission.t) (value : jsil_logic_expr) : unit =
	
	(match SHeap.get heap loc with
	| Some sobj -> 
		(match find_field pfs gamma sobj.fvl field, sobj.domain with
		| Some (field', (orig_perm, _)), _ ->
			(match orig_perm with
			| Readable -> 
				let msg = Printf.sprintf "Non-writable field: (%s, %s)" loc (JSIL_Print.string_of_logic_expression field') in
				raise (Failure msg)
			| _ -> SHeap.set_fv_pair heap loc field' { permission = perm; value = value } )
		| None, Some domain -> 
			let a_set_inclusion = LNot (LSetMem (field, domain)) in 
			if (Pure_Entailment.check_entailment SS.empty (pfs_to_list pfs) [ a_set_inclusion ] gamma) then (
				let new_domain = LSetUnion [ domain; LESet [ field ]] in 
				let new_domain = Simplifications.reduce_expression gamma pfs new_domain in
				let sobj = SObject.set_dom sobj (Some new_domain) in
				SObject.set_fv_pair sobj field { permission = perm; value = value };
				SHeap.set_object heap loc sobj
			) else 
				raise (SymbExecFailure "SHeap.put")
		| _ -> raise (SymbExecFailure "SHeap.put")
		)
	| None -> raise (Failure "Object does not exist.")
	)

let sheap_get 
		(pfs : pure_formulae) (gamma : TypEnv.t) 
		(heap : SHeap.t) (loc : string) (field : jsil_logic_expr) : jsil_logic_expr = 

	(match SHeap.get heap loc with
	| Some sobj -> 
		(match find_field pfs gamma sobj.fvl field, sobj.domain with
		| Some (_, (_, value)), _ -> value
		| None, Some domain -> 
			let a_set_inclusion = LNot (LSetMem (field, domain)) in 
			if (Pure_Entailment.check_entailment SS.empty (pfs_to_list pfs) [ a_set_inclusion ] gamma) 
				then LNone
				else raise (SymbExecFailure "SHeap.get")
		| _ -> raise (SymbExecFailure "SHeap.get"))
	| None -> raise (Failure "Object does not exist.")
	)

let merge_domains 
		(pfs : pure_formulae) (gamma : TypEnv.t)
		(domain_l : jsil_logic_expr option) (domain_r : jsil_logic_expr option) : jsil_logic_expr option = 
		match domain_l, domain_r with 
		| None, None -> None
		| None, Some domain 
		| Some domain, None -> Some domain 
		| Some set1, Some set2 -> 
			let set = LSetUnion [ set1; set2 ] in
			let set = Simplifications.reduce_expression gamma pfs set in
			Some set 

let merge_heaps 
			(store : symbolic_store) (pfs : pure_formulae) (gamma : TypEnv.t)
			(heap : SHeap.t) (new_heap : SHeap.t) : unit =
	
	print_debug_petar (Printf.sprintf "STARTING merge_heaps with heap:\n%s\npat_heap:\n%s\npfs:\n%s\ngamma:\n%s\n"
		(SHeap.str heap) (SHeap.str new_heap)
		(Symbolic_State_Print.string_of_pfs pfs) (TypEnv.str gamma)
	);
		
	let meta_subst = Hashtbl.create 31 in
	
	(* TODO This is a bit strange, what if there are duplicates in the fv lists? Or contradictions with empty_fields and existing cells? TODO *)
	SHeap.iterator new_heap 
		(fun loc (new_sobj : SObject.t) ->
			match SHeap.get heap loc with 
			| Some (old_sobj : SObject.t) -> 
				let extensibility = Extensibility.merge old_sobj.extensibility new_sobj.extensibility in
  				Hashtbl.add meta_subst new_sobj.metadata old_sobj.metadata; 
  				let _ = SFVL.merge_left old_sobj.fvl new_sobj.fvl in
  				let domain = merge_domains pfs gamma old_sobj.domain new_sobj.domain in
  				SHeap.set_object heap loc { old_sobj with domain = domain; extensibility = extensibility }
			| None -> 
				SHeap.set_object heap loc new_sobj);

	(* Substitution *)
	Hashtbl.iter (fun le1 le2 -> 
		(match le1, le2 with
		| Some (ALoc l1), Some (ALoc l2) ->
				print_debug ("Substitution: " ^ l1 ^ " -> " ^ l2); 
				let aloc_subst = init_substitution2 [ l1 ] [ ALoc l2 ] in 
				store_substitution_in_place aloc_subst store;
				pfs_substitution_in_place aloc_subst pfs;
				
				SHeap.substitutionX aloc_subst heap
						
		| Some le1, Some le2 -> if (le1 <> le2) then raise (Failure "Metadata magically different.")
		| _, _ -> ())
	) meta_subst;

	(* Garbage collection - What happens here now?! TODO *)
	SHeap.iterator heap (fun loc sobj -> if (sobj = SObject.empty_object()) then SHeap.remove heap loc);

	print_debug "Finished merging heaps.";
	print_debug (Printf.sprintf "Resulting heap: %s" (SHeap.str heap))


let lexpr_is_none (pfs : pure_formulae) (gamma : TypEnv.t) (le : jsil_logic_expr) : bool option = 
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
		(gamma        : TypEnv.t)
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
	TypEnv.extend gamma_l gamma_r;
	merge_heaps store_l pf_l gamma_l heap_l heap_r;
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
	let pat_gamma = TypEnv.substitution pat_gamma subst false in
	let gamma = TypEnv.copy gamma in
	TypEnv.extend gamma pat_gamma;
	
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
			print_debug_petar (Printf.sprintf "Postcondition is: %s" (Symbolic_State_Print.string_of_symb_state post));
			let new_symb_state = ss_copy symb_state_frame in
			let new_symb_state = merge_symb_states new_symb_state post subst in
			ss_extend_pfs new_symb_state (pfs_of_list pf_discharges);
			let ret_lexpr = store_get_safe (ss_store post) ret_var in
			let ret_lexpr = (match ret_lexpr with
			| None -> print_debug_petar "Warning: Store return variable not present; implicitly empty"; LLit Empty
			| Some le -> let result = JSIL_Logic_Utils.lexpr_substitution subst false le in
			  print_debug_petar (Printf.sprintf "Found return value: %s -> %s" (JSIL_Print.string_of_logic_expression le) (JSIL_Print.string_of_logic_expression result));
				result) in
			[ (new_symb_state, ret_flag, ret_lexpr) ]
		) else [] in 

	List.concat (List.map f_post spec.n_post) 
			

let enrich_pure_part 
	(symb_state     : symbolic_state)
	(symb_state_pat : symbolic_state)
	(subst          : substitution) : bool * symbolic_state =
	
	let pre_gamma = TypEnv.copy (ss_gamma symb_state_pat)     in
	let pre_pfs   = pfs_copy (ss_pfs symb_state_pat)         in	
	let pfs       = pfs_substitution subst false pre_pfs     in
	let gamma     = TypEnv.substitution pre_gamma subst false in
	
	TypEnv.extend gamma (ss_gamma symb_state);
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
	let lheap  = SHeap.get_alocs  heap  in
	let lstore = store_alocs store in
	let lpfs   = pfs_alocs   pfs   in
	let lpreds = preds_alocs preds in
	SS.union lheap (SS.union lstore (SS.union lpfs lpreds))
	
let collect_garbage (symb_state : symbolic_state) = 
	let heap, store, pfs, gamma, preds = symb_state in
	let dangling_locations = Heap.fold
	(fun loc sobj locs ->
		if (sobj = SObject.empty_object()) 
			then SS.add loc locs 
			else locs 
  	)
	heap SS.empty in
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

