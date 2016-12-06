open JSIL_Syntax
open JSIL_Memory_Model

(*************************************)
(** Substitution Functions          **)
(*************************************)

let small_tbl_size = 31

let update_subst1 subst unifier =
	(match unifier with
	 | Some unifier -> List.iter (fun (var, le) -> Hashtbl.add subst var le) unifier;
	 | None -> ());
	true


let update_subst2 subst (unifier1 : (string * jsil_logic_expr) list option)
                        (unifier2 : (string * jsil_logic_expr) list option) p_formulae solver gamma =
	match unifier1, unifier2 with
	| None, None -> true
	| Some _, None -> update_subst1 subst unifier1
	| None, Some _ -> update_subst1 subst unifier2
	| Some unifier1, Some unifier2 ->
	  List.fold_left2 (fun ac (var1, le1) (var2, le2) ->
		if (var1 = var2)
			then
				begin
					if (Pure_Entailment.is_equal le1 le2 p_formulae solver gamma)
						then (Hashtbl.add subst var1 le1; ac)
						else false
				end
			else
				begin
					Hashtbl.add subst var1 le1;
					Hashtbl.add subst var2 le2;
					ac
				end) true unifier1 unifier2

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
						if (is_abs_loc_name loc)
							then
								(if (partial) then (ALoc loc) else
									(let new_aloc = ALoc (fresh_aloc ()) in
									JSIL_Logic_Utils.extend_subst subst loc new_aloc;
									new_aloc))
							else (LLit (Loc loc))) in
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
	(* Printf.printf "Searching for field: %s\n" (JSIL_Print.string_of_logic_expression e false); *)
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

let is_empty_fv_list fv_list =
	let rec loop fv_list =
		match fv_list with
		| [] -> true
		| (_, f_val) :: rest ->
			if (f_val = LNone) then loop rest else false in
	loop fv_list

let is_symb_heap_empty heap =
	LHeap.fold
		(fun loc (fv_list, def) ac -> if (not ac) then ac else is_empty_fv_list fv_list)
		heap
		true


let merge_heaps heap new_heap p_formulae solver gamma =
  (* Printf.printf "-------------------------------------------------------------------\n";
	Printf.printf "-------------INSIDE MERGE HEAPS------------------------------------\n";
	Printf.printf "-------------------------------------------------------------------\n";

	Printf.printf "heap: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_heap heap false);
	Printf.printf "pat_heap: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_heap new_heap false);
	Printf.printf "p_formulae: %s\n" (JSIL_Memory_Print.string_of_shallow_p_formulae p_formulae false);
	Printf.printf "gamma: %s\n" (JSIL_Memory_Print.string_of_gamma gamma); *)

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
							| None, false ->
								(* Printf.printf "i_am_sure_the_field_does_exist: %b\n" i_am_sure_the_field_does_exist; *)
								raise (Failure "heaps non-mergeable")
							| Some (f, v), _ ->
								(* Printf.printf "i_am_sure_the_field_does_exist: %b, (%s, %s)\n"
									i_am_sure_the_field_does_exist (JSIL_Print.string_of_logic_expression f false) (JSIL_Print.string_of_logic_expression v false); *)
								raise (Failure "heaps non-mergeable"))) in
					let q_fv_list = loop [] n_fv_list in
					LHeap.replace heap loc (q_fv_list @ fv_list, def)
				with Not_found ->
					LHeap.add heap loc (n_fv_list, LUnknown))
			| _ -> raise (Failure "heaps non-mergeable: the default field is not unknown!!!"))
		new_heap

	(* Printf.printf "-------------------------------------------------------------------\n";
	Printf.printf "-------------DONE MERGING HEAPS------------------------------------\n";
	Printf.printf "-------------------------------------------------------------------\n";

	Printf.printf "heap: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_heap heap false);
	Printf.printf "pat_heap: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_heap new_heap false);
	Printf.printf "p_formulae: %s\n" (JSIL_Memory_Print.string_of_shallow_p_formulae p_formulae false);
	Printf.printf "gamma: %s\n" (JSIL_Memory_Print.string_of_gamma gamma);

	Printf.printf "-------------------------------------------------------------------\n";
	Printf.printf "-------------NOW WE CONTINUE --------------------------------------\n";
	Printf.printf "-------------------------------------------------------------------\n" *)

let get_heap_vars var_tbl catch_pvars heap =
	LHeap.iter
		(fun _ (fv_list, e_def) ->
			List.iter
				(fun (e_field, e_val) ->
					JSIL_Logic_Utils.get_expr_vars var_tbl catch_pvars e_field;
					JSIL_Logic_Utils.get_expr_vars var_tbl catch_pvars e_val)
				fv_list;
			JSIL_Logic_Utils.get_expr_vars var_tbl catch_pvars e_def)
		heap


let make_all_different_assertion_from_fvlist fv_list : jsil_logic_assertion list =

	let rec make_all_different_assertion_from_field_and_fvlist field fv_list =
		let rec loop fv_list constraints =
			match fv_list with
			| [] -> constraints
			| (f_name, f_val) :: rest ->
				loop rest ((LNot (LEq (field, f_name))) :: constraints) in
		loop fv_list [] in

	let rec loop fields_to_cover fields_covered constraints =
		match fields_to_cover with
		| [] -> constraints
		| (f_name, f_val) :: rest ->
			let new_constraints = make_all_different_assertion_from_field_and_fvlist f_val (fields_covered @ rest) in
			loop rest ((f_name, f_val) :: fields_covered) (new_constraints @ constraints) in

	loop fv_list [] []


let get_heap_well_formedness_constraints heap =
	LHeap.fold
		(fun _ (fv_list, _) constraints ->
			let new_constraints = make_all_different_assertion_from_fvlist fv_list in
			new_constraints @ constraints)
		heap
		[]


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

let get_store_vars var_tbl catch_pvars store =
	Hashtbl.iter (fun _ e -> JSIL_Logic_Utils.get_expr_vars var_tbl catch_pvars e) store

let filter_store store filter_fun =
	Hashtbl.fold
		(fun var le (filtered_vars, unfiltered_vars) ->
			if (filter_fun le)
				then ((var :: filtered_vars), unfiltered_vars)
				else (filtered_vars, (var :: unfiltered_vars)))
		store
		([], [])

let store_projection store vars =
	let les = List.map (fun v -> Printf.printf "So, find me: %s\n" v; Hashtbl.find store v) vars in
	init_store vars les

let check_store store gamma =

	let placeholder pvar le target_type =
		if (Hashtbl.mem gamma pvar) then
		begin
		  let _type = Hashtbl.find gamma pvar in
		  types_leq target_type _type
		end
		else
		begin
		   Hashtbl.add gamma pvar target_type;
		   true
		end in

	Hashtbl.fold
		(fun pvar le ac -> ac &&
			(match le with
			 | LNone -> placeholder pvar le NoneType
			 | ALoc _ -> placeholder pvar le ObjectType
			 | LLit lit -> placeholder pvar le (JSIL_Logic_Utils.evaluate_type_of lit)
			 | _ -> true
			)
		) store true

(*************************************)
(** Pure Formulae functions         **)
(*************************************)
let copy_p_formulae pfs =
	let new_pfs = DynArray.copy pfs in
	new_pfs

let sanitise_pfs dl =
    let length = DynArray.length dl in
	for i = 0 to (length - 1) do
		let el = DynArray.get dl i in
		let rel = JSIL_Logic_Utils.reduce_assertion el in
			DynArray.set dl i rel
	done;
	let ll = DynArray.to_list dl in
	let dindex = DynArray.init length (fun x -> false) in
	let clc = ref 0 in
	let rec find_duplicates l =
		(match l with
		| [] -> ()
		| a :: l ->
			let imem = List.mem a l in
			(if (imem || (a = LTrue)) then
				DynArray.set dindex !clc true);
			clc := !clc + 1;
			find_duplicates l) in
	find_duplicates ll;
	for i = 0 to (length - 1) do
		if (DynArray.get dindex (length - 1 - i))
			then DynArray.delete dl (length - 1 - i)
	done

let extend_pfs pfs solver pfs_to_add =
	(match solver with
	 | None -> ()
	 | Some solver -> solver := None);
	DynArray.append (DynArray.of_list pfs_to_add) pfs;
	sanitise_pfs pfs


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
	DynArray.append pfs_r pfs_l;
	sanitise_pfs pfs_l

(** This function is dramatically incomplete **)
let resolve_location lvar pfs =
	let rec loop pfs =
		match pfs with
		| [] -> None
		| LEq (LVar cur_lvar, ALoc loc) :: rest
		| LEq (ALoc loc, LVar cur_lvar) :: rest  ->
			if (cur_lvar = lvar) then Some (ALoc loc) else loop rest
		| LEq (LVar cur_lvar, LLit (Loc loc)) :: rest
		| LEq (LLit (Loc loc), LVar cur_lvar) :: rest ->
			if (cur_lvar = lvar) then Some (LLit (Loc loc)) else loop rest
		| _ :: rest -> loop rest in
	loop pfs


let get_pf_vars var_tbl catch_pvars pfs =
	let len = DynArray.length pfs in
	for i=0 to len - 1 do
		let a = DynArray.get pfs i in
		JSIL_Logic_Utils.get_ass_vars_iter var_tbl catch_pvars a
	done


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
				(if (partial)
					then	Hashtbl.add new_gamma var v_type
					else (
						if (is_lvar_name var) then (
							let new_lvar = JSIL_Memory_Model.fresh_lvar () in
							Hashtbl.add subst var (LVar new_lvar);
							Hashtbl.add new_gamma new_lvar v_type
						))))
		gamma;
	new_gamma


let is_sensible_subst subst gamma_source gamma_target =
  try
	Hashtbl.iter
		(fun var lexpr ->
			let lexpr_type, _, _ = JSIL_Logic_Utils.type_lexpr gamma_target lexpr in
			let var_type = gamma_get_type gamma_source var in
			(match lexpr_type, var_type with
			| Some le_type, Some v_type ->
			  if (le_type = v_type) then () else raise (Failure (Printf.sprintf "Type mismatch: %s %s"
			  	(JSIL_Print.string_of_type le_type) (JSIL_Print.string_of_type v_type)))
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


let get_gamma_vars var_tbl catch_pvars gamma =
	Hashtbl.iter
		(fun var _ ->
			if (catch_pvars || (is_lvar_name var))
				then Hashtbl.replace var_tbl var true
				else ())
		gamma


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

let find_predicate_assertion preds pred_name =
	let len = DynArray.length preds in
	let rec loop preds args =
		match preds with
		| [] -> args
		| cur_pred :: rest_preds ->
			let cur_pred_name, cur_pred_args = cur_pred in
			if (cur_pred_name = pred_name)
				then loop rest_preds (cur_pred_args :: args)
				else loop rest_preds args  in
	loop (DynArray.to_list preds) []



let predicate_assertion_equality pred pat_pred pfs solver gamma spec_vars =
	Printf.printf "Entering predicate_assertion_equality.\n";

	let spec_vars_str = List.fold_left (fun ac v -> if (ac = "") then v else (ac ^ ", " ^ v)) "" spec_vars in
	let subst = JSIL_Logic_Utils.init_substitution [] in

	let rec unify_pred_args les pat_les =
		(match les, pat_les with
		| [], [] -> Some subst
		| le :: rest_les, pat_le :: rest_pat_les ->
			Printf.printf "I am going to test if %s CAN BE equal to %s\n" (JSIL_Print.string_of_logic_expression le false) (JSIL_Print.string_of_logic_expression pat_le false);
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
	let pred_list = preds_to_list pred_set in
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


let get_preds_vars var_tbl catch_pvars preds =
	let len = DynArray.length preds in
	for i=0 to len - 1 do
		let pred_name, les = DynArray.get preds i in
		List.iter (fun le -> JSIL_Logic_Utils.get_expr_vars var_tbl catch_pvars le) les
	done


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
	extend_pfs (get_pf symb_state) (Some (get_solver symb_state)) pfs_to_add

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


let symb_state_replace_store symb_state new_store =
	let heap, _, pfs, gamma, preds, solver = symb_state in
	(heap, new_store, pfs, gamma, preds, solver)

let symb_state_replace_heap symb_state new_heap =
	let _, store, pfs, gamma, preds, solver = symb_state in
	(new_heap, store, pfs, gamma, preds, solver)

let symb_state_replace_preds symb_state new_preds =
	let heap, store, pfs, gamma, _, solver = symb_state in
	(heap, store, pfs, gamma, new_preds, solver)

let symb_state_replace_gamma symb_state new_gamma =
	let heap, store, pfs, _, preds, solver = symb_state in
	(heap, store, pfs, new_gamma, preds, solver)

let symb_state_replace_pfs symb_state new_pfs =
	let heap, store, _, gamma, preds, solver = symb_state in
	(heap, store, new_pfs, gamma, preds, solver)

let get_symb_state_vars_as_tbl catch_pvars symb_state =
	let var_tbl = Hashtbl.create small_tbl_size in
	let heap, store, pfs, gamma, preds, _ = symb_state in
	get_heap_vars var_tbl catch_pvars heap;
	get_store_vars var_tbl catch_pvars store;
	get_pf_vars var_tbl catch_pvars pfs;
	get_gamma_vars var_tbl catch_pvars gamma;
	get_preds_vars var_tbl catch_pvars preds;
	var_tbl

let get_symb_state_vars_as_list catch_pvars symb_state =
	let var_tbl = get_symb_state_vars_as_tbl catch_pvars symb_state in
	Hashtbl.fold
		(fun v _ ac -> v :: ac)
		var_tbl
		[]


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

(*************************************)
(** Symbolic state simplification   **)
(*************************************)

let isSubstitutable le =
(match le with
 | LLit _ -> true
 | ALoc _ -> true
 | LEList lst ->
     List.fold_left (fun ac x -> ac && (match x with
	   | LLit _ -> true
	   | ALoc _ -> true
	   | _ -> false)) true lst
 | _ -> false
)

let rec aggresively_simplify (to_add : (string * jsil_logic_expr) list) (symb_state : symbolic_state) =

	let f = aggresively_simplify to_add in

	let heap, store, p_formulae, gamma, preds, _ = symb_state in

	let pfs_false msg =
	     print_endline (msg ^ " Pure formulae false.\n");
	     DynArray.clear p_formulae;
		 DynArray.add p_formulae LFalse;
		 f symb_state in

	let rec go_through_pfs (pfs : jsil_logic_assertion list) n =
	(match pfs with
	 | [] ->
	 	(* Printf.printf "To add back: %d equalities\n" (List.length to_add); *)
		List.iter (fun (x, y) -> DynArray.add p_formulae (LEq (LVar x, y))) to_add;
		(* Printf.printf "Done.\nSimplified state:\n%s\n" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state); *)
		symb_state
     | pf :: rest ->
	 	(* Printf.printf "Pure formula: %s\n" (JSIL_Print.string_of_logic_assertion pf false); *)
		(match pf with
		(* We cannot simplify these *)
		| LOr (_, _)
		| LTrue
		| LFalse
		| LLess	(_, _)
		| LLessEq (_, _)
		| LStrLess (_, _) -> go_through_pfs rest (n + 1)

		(* These shouldn't even be here *)
		| LPointsTo	(_, _, _) -> raise (Failure "Heap cell assertion in pure formulae.")
		| LEmp -> raise (Failure "Empty heap assertion in pure formulae.")
		| LPred	(_, _) -> raise (Failure "Predicate in pure formulae.")
		| LTypes _ -> raise (Failure "Types in pure formulae.")

		| LAnd  (a1, a2)
		| LStar	(a1, a2) -> DynArray.set p_formulae n a1; DynArray.add p_formulae a2; f symb_state

		| LNot la ->
		  (match la with
		   | LEq (LLit l1, LLit l2) ->
		   	 (match (l1 = l2) with
			  | true -> pfs_false "Two literals are equal."
			  | false -> DynArray.delete p_formulae n; f symb_state)
		   | _ -> go_through_pfs rest (n + 1)) (* FOR NOW! *)
		| LEq (le1, le2) -> (match (le1 = le2) with
		  | true ->
		  	  DynArray.delete p_formulae n;
		      aggresively_simplify to_add symb_state
		  | false -> (match le1, le2 with
			(* Literals *)
			| LLit l1, LLit l2 ->
			  (match (l1 = l2) with
			   | true -> DynArray.delete p_formulae n; f symb_state
			   | false -> pfs_false "Two literals are not equal.")
			  (* Variable and a literal: substitute in heap, substitute in store, substitute in pfs, kill in gamma *)
 			| LVar var, _ when (isSubstitutable le2) ->
 			  (* create substitution *)
 			  let subst = Hashtbl.create 1 in
 		      Hashtbl.add subst var le2;
 			  DynArray.delete p_formulae n;
 			  (* understand deletion *)
 			  let it_stays = (String.get var 0 = '#') in
 		      let new_to_add =
 			  (match it_stays with
 			   | false ->
 			       while (Hashtbl.mem gamma var) do Hashtbl.remove gamma var done;
 				   to_add
 			   | true ->
 				 (* Printf.printf "Adding: (%s, %s)\n" var (JSIL_Print.string_of_logic_expression le2 false); *)
 			     ((var, le2) :: to_add)
 			   ) in
 			   let symb_state = symb_state_substitution symb_state subst true in
 			   let to_add = List.map (fun (var, le) -> (var, JSIL_Logic_Utils.lexpr_substitution le subst true)) to_add in
 			   aggresively_simplify new_to_add symb_state

			(*
			 * Lists
			 *
			 * 1) Two logical lists - lengths must match, element equality, restart
			 *)
			| LEList ll1, LEList ll2 ->
			  let len1 = List.length ll1 in
			  let len2 = List.length ll2 in
			  if (len1 = len2) then
			  begin
				DynArray.delete p_formulae n;
				List.iter2 (fun x y -> DynArray.add p_formulae (LEq (x, y))) ll1 ll2;
				f symb_state
			  end
			  else pfs_false "Lists are not of the same length."
			(* Lists
			 *
			 * 2) One logical, one literal list - lengths must match, element equality, restart
			 *)
			| LEList ll1, LLit (LList ll2)
			| LLit (LList ll2), LEList ll1 ->
			  let len1 = List.length ll1 in
			  let len2 = List.length ll2 in
			  if (len1 = len2) then
			  begin
				DynArray.delete p_formulae n;
				List.iter2 (fun x y -> DynArray.add p_formulae (LEq (x, LLit y))) ll1 ll2;
				f symb_state
			  end
			  else pfs_false "Lists are not of the same length."
			(* Injective operators *)
			| LUnOp (ToStringOp, le1), LUnOp (ToStringOp, le2) ->
			  DynArray.set p_formulae n (LEq (le1, le2));
			  aggresively_simplify to_add symb_state
			| LStrNth (le1, le2), LStrNth (le3, le4) ->
			  if (le1 = le2) then
			  begin
				DynArray.set p_formulae n (LEq (le2, le4));
				aggresively_simplify to_add symb_state
			  end else go_through_pfs rest (n + 1)
			(* Whatever else *)
			| _, _ -> go_through_pfs rest (n + 1)
			)
		  )
		)
	) in (*)
		  if (le1 = le2) then
		  begin

		  end else
		  begin
			(match le1, le2 with
			 (* Two variables *)
			 | LVar chantay_you_stay, LVar sashay_away ->
			   if ((String.get chantay_you_stay 0 = '_') && (String.get sashay_away 0 = '_')) then
			   begin
			   	   (* Printf.printf "LVAR: Substituting %s for %s\n" chantay_you_stay sashay_away; *)
	 			   let subst = Hashtbl.create 1 in
	 			   Hashtbl.add subst sashay_away (LVar chantay_you_stay);
	 			   DynArray.delete p_formulae n;
				   while (Hashtbl.mem gamma sashay_away) do Hashtbl.remove gamma sashay_away done;
				   let symb_state = symb_state_substitution symb_state subst true in
				   let to_add = List.map (fun (var, le) -> (var, JSIL_Logic_Utils.lexpr_substitution le subst true)) to_add in
	 			   aggresively_simplify to_add symb_state
			   end
			   else go_through_pfs rest (n + 1)



			 (* Whatever else *)
			 | _, _ -> go_through_pfs rest (n + 1)
			)
	      end
		)
	)
	in *)

	(* Printf.printf "Simplification:\n%s\n" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state); *)

	DynArray.iteri
	(fun i pf ->
	  (match pf with
	   | LEq (LVar _, LVar _) -> ()
	   | LEq (le1, LVar var) -> DynArray.set p_formulae i (LEq (LVar var, le1))
	   | _ -> ()
	  )
	) p_formulae;

	sanitise_pfs p_formulae;

	let pf_list = DynArray.to_list p_formulae in
		go_through_pfs pf_list 0
