open JSIL_Syntax
open JSIL_Memory_Model

(*************************************)
(** Substitution Functions          **)
(*************************************)

let update_subst1 subst unifier =
	match unifier with
	| false, _ -> false
	| _, Some (var, le) ->
		 Hashtbl.add subst var le;
		true
	| _, None -> true


let update_subst2 subst unifier1 unifier2 p_formulae solver gamma =
	match unifier1, unifier2 with
	| (true, None), (true, None) -> true

	| (true, Some _), (true, None) -> update_subst1 subst unifier1

	| (true, None), (true, Some _) -> update_subst1 subst unifier2

	| (true, Some (var1, le1)), (true, Some (var2, le2)) ->
		if (var1 = var2)
			then
				begin
					if (Pure_Entailment.is_equal le1 le2 p_formulae solver gamma)
						then (Hashtbl.add subst var1 le1; true)
						else false
				end
			else
				begin
					Hashtbl.add subst var1 le1;
					Hashtbl.add subst var2 le2;
					true
				end

	| _, _ -> false



(*************************************)
(** Abstract Heap functions         **)
(*************************************)
let fv_list_substitution fv_list subst partial =
	List.map
		(fun (le_field, le_val) ->
			let s_le_field = JSIL_Logic_Utils.lexpr_substitution le_field subst partial in
			let s_le_val = JSIL_Logic_Utils.lexpr_substitution le_val subst partial in
			(s_le_field, s_le_val))
		fv_list


let heap_substitution (heap : symbolic_heap) (subst : substitution) partial =
	let new_heap = LHeap.create 1021 in
	LHeap.iter
		(fun loc (fv_list, def) ->
			let s_loc =
				(try Hashtbl.find subst loc
					with _ ->
						(* Printf.printf "this location is not in the substitution. es estupido nao?!!!!!\n\n\n"; *)
						if (partial) then
							if (is_abs_loc_name loc) then (ALoc loc) else (LLit (Loc loc))
						else
							begin
								let new_aloc = ALoc (fresh_aloc ()) in
								JSIL_Logic_Utils.extend_subst subst loc new_aloc;
								new_aloc
							end) in
			let s_loc =
				(match s_loc with
					| LLit (Loc loc) -> loc
					| ALoc loc -> loc
					| _ ->
						(* Printf.printf "This is a disaster!!"; *)
						raise (Failure "Heap substitution failed miserably!!!")) in
			let s_fv_list = fv_list_substitution fv_list subst partial in
			let s_def = JSIL_Logic_Utils.lexpr_substitution def subst partial in
			LHeap.add new_heap s_loc (s_fv_list, s_def))
		heap;
	new_heap


(**
  find_field fv_list e p_formulae = fv_list', (e1, e2)
	   st:
		    fv_list = fv_list' U (e1, e2)
				and
				pure_formulae |=

*)
let find_field loc fv_list e p_formulae solver gamma =
	let rec find_field_rec fv_list traversed_fv_list i_am_sure_the_field_does_not_exist =
		match fv_list with
		| [] -> traversed_fv_list, None, i_am_sure_the_field_does_not_exist
		| (e_field, e_value) :: rest ->
			(if (Pure_Entailment.is_equal e e_field p_formulae solver gamma)
				then traversed_fv_list @ rest, Some (e_field, e_value), false
				else
					(if (i_am_sure_the_field_does_not_exist && (Pure_Entailment.is_different e e_field p_formulae solver gamma))
						then find_field_rec rest ((e_field, e_value) :: traversed_fv_list) true
						else find_field_rec rest ((e_field, e_value) :: traversed_fv_list) false)) in
	find_field_rec fv_list [] true


let update_abs_heap_default (heap : symbolic_heap) loc e =
	let fv_list, default_val = try LHeap.find heap loc with _ -> [], LUnknown in
	match default_val with
	| LUnknown -> LHeap.replace heap loc (fv_list, e)
 	| _ -> raise (Failure "the default value for the fields of a given object cannot be changed once set")


let update_abs_heap (heap : symbolic_heap) loc e_field e_val p_formulae solver gamma =
	(* Printf.printf "Update Abstract Heap\n"; *)
	let fv_list, default_val = try LHeap.find heap loc with _ -> [], LUnknown in
	let unchanged_fv_list, field_val_pair, i_am_sure_the_field_does_not_exist = find_field loc fv_list e_field p_formulae solver gamma in
	match field_val_pair, i_am_sure_the_field_does_not_exist with
	| Some _, _
	| None, true -> LHeap.replace heap loc ((e_field, e_val) :: unchanged_fv_list, default_val)
	| None, false ->
		let msg = Printf.sprintf "Cannot decide if %s exists in object %s" (JSIL_Print.string_of_logic_expression e_field false) loc in
			raise (Failure msg)


let abs_heap_find heap l e p_formulae solver gamma =
	let fv_list, default_val = try LHeap.find heap l with _ -> [], LUnknown in
	let _, field_val_pair, i_am_sure_the_field_does_not_exist = find_field l fv_list e p_formulae solver gamma in
	match field_val_pair, i_am_sure_the_field_does_not_exist with
	| Some (_, f_val), _ -> f_val
	| None, true -> default_val
	| None, false ->
		let msg = Printf.sprintf "Cannot decide if %s exists in object %s" (JSIL_Print.string_of_logic_expression e false) l in
			raise (Failure msg)

let abs_heap_check_field_existence heap l e p_formulae solver gamma =
	let f_val = abs_heap_find heap l e p_formulae solver gamma in
	match f_val with
	| LUnknown -> None
	| LNone -> Some false
	|	_ ->
		if (Pure_Entailment.is_equal f_val LNone p_formulae solver gamma) then
			(Some false)
			else (if (Pure_Entailment.is_different f_val LNone p_formulae solver gamma) then
				(Some true)
				else None)

let abs_heap_delete heap l e p_formulae solver gamma =
	let fv_list, default_val = try LHeap.find heap l with _ -> [], LUnknown in
	let rest_fv_pairs, del_fv_pair, _ = find_field l fv_list e p_formulae solver gamma in
	match del_fv_pair with
	| Some (_, _) -> LHeap.replace heap l (rest_fv_pairs, default_val)
	| None -> raise (Failure "Trying to delete an inexistent field")


let is_symb_heap_empty heap =
	LHeap.fold
		(fun loc (fv_list, def) ac ->
			match fv_list with
			| [] -> ac
			| _ -> false)
		heap
		true


let merge_heaps heap new_heap p_formulae solver gamma =
	(* Printf.printf "-------------------------------------------------------------------\n";
	Printf.printf "-------------INSIDE MERGE HEAPS------------------------------------\n";
	Printf.printf "-------------------------------------------------------------------\n";

	Printf.printf "heap: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_heap heap false);
	Printf.printf "pat_heap: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_heap new_heap false);
	Printf.printf "p_formulae: %s\n" (JSIL_Memory_Print.string_of_shallow_p_formulae p_formulae false); *)
	LHeap.iter
		(fun loc (n_fv_list, n_def) ->
			match n_def with
			| LUnknown ->
				(try
					let fv_list, def = LHeap.find heap loc in
					let rec loop q_fv_list n_fv_list =
						(match n_fv_list with
						| [] -> q_fv_list
						| (le_field, le_val) :: rest_n_fv_list ->
							(* Printf.printf "le_field: %s, le_val: %s\n" (JSIL_Print.string_of_logic_expression le_field false) (JSIL_Print.string_of_logic_expression le_val false); *)
							let _, fv_pair, i_am_sure_the_field_does_exist = find_field loc fv_list le_field p_formulae solver gamma in
							(match fv_pair, i_am_sure_the_field_does_exist with
							| None, true -> loop ((le_field, le_val) :: q_fv_list) rest_n_fv_list
							| None, false
							| Some _, _ ->
								Printf.printf "i_am_sure_the_field_does_exist: %b\n" i_am_sure_the_field_does_exist;
								raise (Failure "heaps non-mergeable"))) in
					let q_fv_list = loop [] n_fv_list in
					LHeap.replace heap loc (q_fv_list @ fv_list, def)
				with Not_found ->
					LHeap.add heap loc (n_fv_list, LUnknown))
			| _ -> raise (Failure "heaps non-mergeable: the default field is not unknwon!!!"))
		new_heap

(*************************************)
(** Abstract Store functions        **)
(*************************************)

let init_store vars les =
	let store = Hashtbl.create 31 in

	let rec loop vars les =
		match vars, les with
		| [], _ -> ()
		| var :: rest_vars, le :: rest_les ->
				Hashtbl.replace store var le; loop rest_vars rest_les
		| var :: rest_vars, [] ->
				Hashtbl.replace store var (LLit Undefined); loop rest_vars [] in

	loop vars les;
	store

let store_substitution store gamma subst partial =
	let vars, les =
		Hashtbl.fold
			(fun pvar le (vars, les) ->
						let s_le = JSIL_Logic_Utils.lexpr_substitution le subst partial in
						let s_le_type, is_typable, _ = JSIL_Logic_Utils.type_lexpr gamma s_le in
						(match s_le_type with
							| Some s_le_type ->
							(* Printf.printf "I am adding the type of %s to the store with   *)
							(* type %s\n" pvar (JSIL_Print.string_of_type s_le_type);        *)
									Hashtbl.replace gamma pvar s_le_type
							|	None -> ());
						(pvar :: vars), (s_le :: les))
			store
			([], []) in
	let store = init_store vars les in
	store




(*************************************)
(** Pure Formulae functions         **)
(*************************************)
let copy_p_formulae pfs =
	let new_pfs = DynArray.copy pfs in

	new_pfs


let extend_pf pfs solver pfs_to_add =
	let is_pf_fresh pf_to_add =
		(DynArray.fold_left
			(fun ac pf -> (ac && (not (pf = pf_to_add))))
			true
			pfs) in

	let is_pf_sensible pf_to_add =
		(match pf_to_add with
		| LEq (le1, le2) -> (not (le1 = le2))
		| LTrue          -> false
		| _              -> true) in

	let rec loop pfs_to_add fresh_pfs_to_add =
		match pfs_to_add with
		| [] -> fresh_pfs_to_add
		| pf_to_add :: rest_pfs_to_add ->
			if ((is_pf_sensible pf_to_add) && (is_pf_fresh pf_to_add))
				then loop rest_pfs_to_add (pf_to_add :: fresh_pfs_to_add)
				else loop rest_pfs_to_add fresh_pfs_to_add in
	(* Printf.printf "I am deleting the solver!!!\n"; *)
	solver := None;
	DynArray.append (DynArray.of_list (loop pfs_to_add [])) pfs


let pf_of_store store subst =
	Hashtbl.fold
		(fun var le pfs ->
			try
				let sle = Hashtbl.find subst var in
				((LEq (sle, le)) :: pfs)
			with _ -> pfs)
		store
		[]


let pf_of_store2 store =
	Hashtbl.fold
		(fun var le pfs -> ((LEq (PVar var, le)) :: pfs))
		store
		[]


let pf_of_substitution subst =
	Hashtbl.fold
		(fun var le pfs ->
			if (is_lvar_name var)
				then ((LEq (LVar var, le)) :: pfs)
				else pfs)
		subst
		[]

let pf_substitution pf_r subst partial =
	(* *)
	let new_pf = DynArray.create () in
	let len = (DynArray.length pf_r) - 1 in
	for i=0 to len do
		let a = DynArray.get pf_r i in
		let s_a = JSIL_Logic_Utils.assertion_substitution a subst partial in
		DynArray.add new_pf s_a
	done;
	new_pf

let merge_pfs pfs_l pfs_r =
  DynArray.append pfs_r pfs_l

(** This function is dramatically incomplete **)
let resolve_location lvar pfs =
	let rec loop pfs =
		match pfs with
		| [] -> None
		| LEq (LVar lvar, ALoc loc) :: rest
		| LEq (ALoc loc, LVar lvar) :: rest  -> Some (ALoc loc)
		| LEq (LVar lvar, LLit (Loc loc)) :: rest
		| LEq (LLit (Loc loc), LVar lvar) :: rest -> Some (LLit (Loc loc))
		| _ :: rest -> loop rest in
	loop pfs

(*************************************)
(** Typing Environment functions    **)
(*************************************)
let rec gamma_substitution gamma subst partial =
	let new_gamma = Hashtbl.create 31 in
	Hashtbl.iter
		(fun var v_type ->
			try
			let new_var = Hashtbl.find subst var in
			(match new_var with
			| LVar new_var -> Hashtbl.replace new_gamma new_var v_type
			| _ ->
				(if (partial) then
					Hashtbl.add new_gamma var v_type))
			with _ ->
				(if (partial) then
					Hashtbl.add new_gamma var v_type))
		gamma;
	new_gamma

let is_sensible_subst subst gamma =
    try
	Hashtbl.iter
		(fun var lexpr ->
			let lexpr_type, _, _ = JSIL_Logic_Utils.type_lexpr gamma lexpr in
			let var_type = gamma_get_type gamma var in
			(match lexpr_type, var_type with
			| Some le_type, Some v_type ->
			  if (le_type = v_type) then () else raise (Failure (Printf.sprintf "Type mismatch: %s %s"
			  	(JSIL_Print.string_of_type le_type) (JSIL_Print.string_of_type v_type)))
			| None, Some v_type -> raise (Failure "Gamma typed, unfold untyped")
			| _, _ -> ()))
		subst;
	true
	with (Failure msg) -> Printf.printf "%s\n" msg; false

let merge_gammas (gamma_l : typing_environment) (gamma_r : typing_environment) =
	Hashtbl.iter
		(fun var v_type ->
			if (not (Hashtbl.mem gamma_l var))
				then Hashtbl.add gamma_l var v_type)
		gamma_r


(*************************************)
(** Predicate Set functions         **)
(*************************************)
let pred_substitution pred subst partial =
	let pred_name, les = pred in
	let s_les = List.map (fun le -> JSIL_Logic_Utils.lexpr_substitution le subst partial)  les in
	(pred_name, s_les)

let preds_substitution preds subst partial =
	let len = DynArray.length preds in
	let new_preds = DynArray.create () in
	for i=0 to len - 1 do
		let pred = DynArray.get preds i in
		let s_pred = pred_substitution pred subst partial in
		(* Printf.printf "len: %i. i: %i. pred: %s. s_pred: %s\n" len i (JSIL_Memory_Print.string_of_pred pred) (JSIL_Memory_Print.string_of_pred s_pred); *)
		DynArray.add new_preds s_pred
	done;
	new_preds


let predicate_assertion_equality pred pat_pred pfs solver gamma spec_vars =
	let spec_vars_str = List.fold_left (fun ac v -> if (ac = "") then v else (ac ^ ", " ^ v)) "" spec_vars in
	let subst = JSIL_Logic_Utils.init_substitution [] in

	let rec unify_pred_args les pat_les =
		(match les, pat_les with
		| [], [] -> Some subst
		| le :: rest_les, pat_le :: rest_pat_les ->
			(* Printf.printf "I am going to test if %s CAN BE equal to %s\n" (JSIL_Print.string_of_logic_expression le1 false) (JSIL_Print.string_of_logic_expression le2 false); *)
			(match pat_le with
			| LVar l2 when (not (List.mem l2 spec_vars)) ->
				JSIL_Logic_Utils.extend_subst subst l2 le;
				unify_pred_args rest_les rest_pat_les
			| _ ->
				if (Pure_Entailment.is_equal le pat_le pfs solver gamma)
					then unify_pred_args rest_les rest_pat_les
					else None)) in

	match pred, pat_pred with
	| (name, les), (pat_name, pat_les) ->
		if (name = pat_name) then
			unify_pred_args les pat_les
		else None
	| _, _ -> raise (Failure "predicate_assertion_equality: FATAL ERROR")

let subtract_pred pred_name args pred_set pfs solver gamma spec_vars =
	let pred_list = DynArray.to_list pred_set in
	let rec loop pred_list index =
		(match pred_list with
		| [] -> raise (Failure (Printf.sprintf "Predicate %s not found in the predicate set!!!" pred_name))
		| pred :: rest_pred_list ->
			(match (predicate_assertion_equality pred (pred_name, args) pfs solver gamma spec_vars) with
			| None -> loop rest_pred_list (index + 1)
			| Some subst -> index, subst)) in

	let index, subst = loop pred_list 0 in
	DynArray.delete pred_set index;
	subst

let is_preds_empty preds =
	(DynArray.length preds) = 0


(*************************************)
(** Symbolic State functions        **)
(*************************************)
let copy_symb_state symb_state =
	let heap, store, p_formulae, gamma, preds, solver = symb_state in
	let c_heap      = LHeap.copy heap in
	let c_store     = copy_store store in
	let c_pformulae = copy_p_formulae p_formulae in
	let c_gamma     = copy_gamma gamma in
	let c_preds     = copy_pred_set preds in
	(match !solver with 
	| Some (solver, _) -> Z3.Solver.reset solver
	| None -> ()); 
	(c_heap, c_store, c_pformulae, c_gamma, c_preds, ref None)

let rec extend_symb_state_with_pfs symb_state pfs_to_add =
	extend_pf (get_pf symb_state) (get_solver symb_state) pfs_to_add

let symb_state_substitution (symb_state : symbolic_state) subst partial =
	let heap, store, pf, gamma, preds, _ = symb_state in
	let s_heap = heap_substitution heap subst partial in
	let s_store = store_substitution store gamma subst partial in
	let s_pf = pf_substitution pf subst partial  in
	(*Printf.printf "partial: %b. the gamma as it is now: %s.\n" partial (JSIL_Memory_Print.string_of_gamma gamma); *)
	let s_gamma = gamma_substitution gamma subst partial in
	let s_preds = preds_substitution preds subst partial in
	(s_heap, s_store, s_pf, s_gamma, s_preds, ref None)

let symb_state_add_subst_as_equalities new_symb_state subst pfs spec_vars =
	Hashtbl.iter
		(fun var le ->
			match le with
			| LLit _
			| ALoc _ ->
				if (List.mem var spec_vars)
					then DynArray.add pfs (LEq (LVar var, le))
					else ()
			| _ -> DynArray.add pfs (LEq (LVar var, le)))
		subst

let is_empty_symb_state symb_state =
	(is_symb_heap_empty (get_heap symb_state)) && (is_preds_empty (get_preds symb_state))

let merge_symb_states (symb_state_l : symbolic_state) (symb_state_r : symbolic_state) subst  : symbolic_state =
	(* *)

	(* Printf.printf "gamma_r: %s\n." (JSIL_Memory_Print.string_of_gamma (get_gamma symb_state_r)); *)
	(* Printf.printf "substitution: %s\n" (JSIL_Memory_Print.string_of_substitution subst); *)

	let symb_state_r = symb_state_substitution symb_state_r subst false in
	let heap_l, store_l, pf_l, gamma_l, preds_l, solver_l = symb_state_l in
	let heap_r, store_r, pf_r, gamma_r, preds_r, _ = symb_state_r in

	(* DynArray.append pf_r pf_l; *)
	merge_pfs pf_l pf_r;
	merge_gammas gamma_l gamma_r;

	(* Printf.printf "BEFORE MERGING HEAPS. pfs_l: %s\n. pfs_r: %s\n." (JSIL_Memory_Print.string_of_shallow_p_formulae pf_l false)
		(JSIL_Memory_Print.string_of_shallow_p_formulae pf_r false); *)
	merge_heaps heap_l heap_r pf_l solver_l gamma_l;
	(* Printf.printf "AFTER MERGING HEAPS\n\n"; *)

	DynArray.append preds_r preds_l;
	(* *)
	(* Printf.printf "s_heap_l after merge: %s.\ns_preds_l: %s.\ns_store_l: %s.\n" (JSIL_Memory_Print.string_of_shallow_symb_heap heap_l)
		(JSIL_Memory_Print.string_of_preds preds_l) (JSIL_Memory_Print.string_of_shallow_symb_store store_l); *)
	(* *)
	(heap_l, store_l, pf_l, gamma_l, preds_l, (ref None))


let symb_state_replace_store symb_state new_store =
	let heap, _, pfs, gamma, preds = symb_state in
	(heap, new_store, pfs, gamma, preds)

let symb_state_replace_heap symb_state new_heap =
	let _, store, pfs, gamma, preds, solver = symb_state in
	(new_heap, store, pfs, gamma, preds, solver)

let symb_state_replace_preds symb_state new_preds =
	let heap, store, pfs, gamma, _, solver = symb_state in
	(heap, store, pfs, gamma, new_preds, solver)

let symb_state_replace_gamma symb_state new_gamma =
	let heap, store, pfs, _, preds, solver = symb_state in
	(heap, store, pfs, new_gamma, preds, solver)

(*************************************)
(** Normalised Spec functions       **)
(*************************************)
let copy_single_spec s_spec =
	let copy_pre  = copy_symb_state s_spec.n_pre in
	let copy_post = List.map copy_symb_state s_spec.n_post in
	{
		n_pre        = copy_pre;
		n_post       = s_spec.n_post;
		n_ret_flag   = s_spec.n_ret_flag;
		n_lvars      = s_spec.n_lvars;
		n_post_lvars = s_spec.n_post_lvars;
		n_subst      = s_spec.n_subst
	}
