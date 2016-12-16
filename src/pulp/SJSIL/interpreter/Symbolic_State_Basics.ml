open JSIL_Syntax
open JSIL_Memory_Model
open JSIL_Logic_Utils

(*************************************)
(** Abstract Heap functions         **)
(*************************************)

let is_empty_fv_list fv_list =
	let rec loop fv_list =
		match fv_list with
		| [] -> true
		| (_, f_val) :: rest ->
			if (f_val = LNone) then loop rest else false in
	loop fv_list

let fv_list_substitution fv_list subst partial =
	List.map
		(fun (le_field, le_val) ->
			let s_le_field = lexpr_substitution le_field subst partial in
			let s_le_val = lexpr_substitution le_val subst partial in
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
									extend_subst subst loc new_aloc;
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
			let s_def = lexpr_substitution def subst partial in
			LHeap.add new_heap s_loc (s_fv_list, s_def))
		heap;
	new_heap

let is_symb_heap_empty heap =
	LHeap.fold
		(fun loc (fv_list, def) ac -> if (not ac) then ac else is_empty_fv_list fv_list)
		heap
		true

let get_heap_vars var_tbl catch_pvars heap =
	LHeap.iter
		(fun _ (fv_list, e_def) ->
			List.iter
				(fun (e_field, e_val) ->
					get_expr_vars var_tbl catch_pvars e_field;
					get_expr_vars var_tbl catch_pvars e_val)
				fv_list;
			get_expr_vars var_tbl catch_pvars e_def)
		heap

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
						let s_le = lexpr_substitution le subst partial in
						let s_le_type, is_typable, _ = type_lexpr gamma s_le in
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
	Hashtbl.iter (fun _ e -> get_expr_vars var_tbl catch_pvars e) store

let filter_store store filter_fun =
	Hashtbl.fold
		(fun var le (filtered_vars, unfiltered_vars) ->
			if (filter_fun le)
				then ((var :: filtered_vars), unfiltered_vars)
				else (filtered_vars, (var :: unfiltered_vars)))
		store
		([], [])

let store_projection store vars =
	let les = List.map (fun v -> print_debug (Printf.sprintf "So, find me: %s\n" v); Hashtbl.find store v) vars in
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
			 | LLit lit -> placeholder pvar le (evaluate_type_of lit)
			 | _ -> true
			)
		) store true

(*************************************)
(** Pure Formulae functions         **)
(*************************************)

let copy_p_formulae pfs =
	let new_pfs = DynArray.copy pfs in
	new_pfs

(* let extend_pfs pfs solver pfs_to_add =
	print_time_debug "extend_pfs:";
	(match solver with
	 | None -> ()
	 | Some solver -> solver := None);
	DynArray.append (DynArray.of_list pfs_to_add) pfs *)

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
		let s_a = assertion_substitution a subst partial in
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
		get_ass_vars_iter var_tbl catch_pvars a
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
			let lexpr_type, _, _ = type_lexpr gamma_target lexpr in
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
	let s_les = List.map (fun le -> lexpr_substitution le subst partial)  les in
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

let is_preds_empty preds =
	(DynArray.length preds) = 0


let get_preds_vars var_tbl catch_pvars preds =
	let len = DynArray.length preds in
	for i=0 to len - 1 do
		let pred_name, les = DynArray.get preds i in
		List.iter (fun le -> get_expr_vars var_tbl catch_pvars le) les
	done

(*************************************)
(** Symbolic State functions        **)
(*************************************)

let copy_symb_state symb_state =
	let heap, store, p_formulae, gamma, preds (*, solver*) = symb_state in
	let c_heap      = LHeap.copy heap in
	let c_store     = copy_store store in
	let c_pformulae = copy_p_formulae p_formulae in
	let c_gamma     = copy_gamma gamma in
	let c_preds     = copy_pred_set preds in
	(* (match !solver with
	| Some (solver, _) -> Z3.Solver.reset solver
	| None -> ()); *)
	(c_heap, c_store, c_pformulae, c_gamma, c_preds (*, ref None *))

let rec extend_symb_state_with_pfs symb_state pfs_to_add =
	merge_pfs (get_pf symb_state) pfs_to_add

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
	let heap, _, pfs, gamma, preds (*, solver *) = symb_state in
	(heap, new_store, pfs, gamma, preds (*, solver *))

let symb_state_replace_heap symb_state new_heap =
	let _, store, pfs, gamma, preds (*, solver *) = symb_state in
	(new_heap, store, pfs, gamma, preds (*, solver *))

let symb_state_replace_preds symb_state new_preds =
	let heap, store, pfs, gamma, _ (*, solver *) = symb_state in
	(heap, store, pfs, gamma, new_preds (*, solver *))

let symb_state_replace_gamma symb_state new_gamma =
	let heap, store, pfs, _, preds (*, solver *) = symb_state in
	(heap, store, pfs, new_gamma, preds (*, solver *))

let symb_state_replace_pfs symb_state new_pfs =
	let heap, store, _, gamma, preds (*, solver *) = symb_state in
	(heap, store, new_pfs, gamma, preds (*, solver *))

let get_symb_state_vars_as_tbl catch_pvars symb_state =
	let var_tbl = Hashtbl.create small_tbl_size in
	let heap, store, pfs, gamma, preds (*, _*) = symb_state in
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

let symb_state_substitution (symb_state : symbolic_state) subst partial =
	let heap, store, pf, gamma, preds (*, _ *) = symb_state in
	let s_heap = heap_substitution heap subst partial in
	let s_store = store_substitution store gamma subst partial in
	let s_pf = pf_substitution pf subst partial  in
	(*Printf.printf "partial: %b. the gamma as it is now: %s.\n" partial (JSIL_Memory_Print.string_of_gamma gamma); *)
	let s_gamma = gamma_substitution gamma subst partial in
	let s_preds = preds_substitution preds subst partial in
	(s_heap, s_store, s_pf, s_gamma, s_preds (* ref None *))

(*************************************)
(** Symbolic state simplification   **)
(*************************************)

let reduce_pfs_no_store_no_gamma pfs = DynArray.map (fun x -> reduce_assertion_no_store_no_gamma pfs x) pfs
let reduce_pfs_no_store    gamma pfs = DynArray.map (fun x -> reduce_assertion_no_store    gamma pfs x) pfs
let reduce_pfs    store    gamma pfs = DynArray.map (fun x -> reduce_assertion    store    gamma pfs x) pfs

let reduce_pfs_in_place store gamma pfs =
	let pfs_old = DynArray.copy pfs in
    let length = DynArray.length pfs in
	let changed = ref false in
	for i = 0 to (length - 1) do
		let el = DynArray.get pfs i in
		let rel = reduce_assertion store gamma pfs el in
			changed := !changed && (el = rel);
			DynArray.set pfs i rel
	done ;
	if !changed then print_debug (Printf.sprintf "Reduce pfs in place: %s ---> %s"
		(JSIL_Memory_Print.string_of_shallow_p_formulae pfs_old false)
		(JSIL_Memory_Print.string_of_shallow_p_formulae pfs false))

let sanitise_pfs store gamma pfs =
    reduce_pfs_in_place store gamma pfs;

	let length = DynArray.length pfs in
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
	let ll = DynArray.to_list pfs in
	find_duplicates ll;
	for i = 0 to (length - 1) do
		if (DynArray.get dindex (length - 1 - i))
			then DynArray.delete pfs (length - 1 - i)
	done

let sanitise_pfs_no_store_no_gamma = sanitise_pfs (Hashtbl.create 1) (Hashtbl.create 1)
let sanitise_pfs_no_store          = sanitise_pfs (Hashtbl.create 1)

let allowedListMember le =
(match le with
 | LLit _ -> true
 | ALoc _ -> true
 | LVar var -> true
 | _ -> false)

let rec isSubstitutable le =
(match le with
 | LLit _ -> true
 | ALoc _ -> true
 | LEList lst ->
     List.fold_left (fun ac x -> ac && allowedListMember x) true lst
 | LBinOp (le, LstCons, lst) ->
     allowedListMember le && isSubstitutable lst
 | _ -> false
)

let rec isExistentiallySubstitutable le =
(match le with
 | LLit _ -> true
 | ALoc _ -> true
 | LVar _ -> true
 | LEList les -> List.fold_left
     (fun ac x -> ac & isExistentiallySubstitutable x) true les
 | LBinOp (le, LstCons, les) -> isExistentiallySubstitutable le && isExistentiallySubstitutable les
 | _ -> false
)

let rec aggressively_simplify (to_add : (string * jsil_logic_expr) list) other_pfs save_all_lvars (symb_state : symbolic_state) : (symbolic_state * jsil_logic_assertion DynArray.t) =

	let f = aggressively_simplify to_add other_pfs save_all_lvars in

	let heap, store, p_formulae, gamma, preds (*, _ *) = symb_state in

	let pfs_false msg =
	   print_debug (msg ^ " Pure formulae false.\n");
	   DynArray.clear p_formulae;
		 DynArray.add p_formulae LFalse;
		 DynArray.clear other_pfs;
		 symb_state, other_pfs in

	let rec go_through_pfs (pfs : jsil_logic_assertion list) n =
	(match pfs with
	 | [] ->
	 	(* print_debug (Printf.sprintf "To add back: %d equalities\n" (List.length to_add)); *)
		List.iter (fun (x, y) -> DynArray.add p_formulae (LEq (LVar x, y))) to_add;
		print_debug (Printf.sprintf "Simplified state:\n%s\n" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state));
		symb_state, other_pfs
     | pf :: rest ->
	 	(* print_debug (Printf.sprintf "Pure formula: %s" (JSIL_Print.string_of_logic_assertion pf false)); *)
		(match pf with
		(* We cannot simplify these *)
		| LOr (_, _)
		| LTrue
		| LStrLess (_, _) -> go_through_pfs rest (n + 1)

		| LFalse -> pfs_false "This is exceptionally bad."

		| LLess	(le1, le2) ->
		  (match le1, le2 with
		   | LLit (Integer n1), LLit (Integer n2) ->
				let result = if (n1 < n2) then LTrue else LFalse in
				DynArray.set p_formulae n result; f symb_state
		   | LLit (Integer n1), LLit (Num n2) ->
				let result = if (float_of_int n1 < n2) then LTrue else LFalse in
				DynArray.set p_formulae n result; f symb_state
		   | LLit (Num n1), LLit (Integer n2) ->
				let result = if (n1 < float_of_int n2) then LTrue else LFalse in
				DynArray.set p_formulae n result; f symb_state
		   | LLit (Num n1), LLit (Num n2) ->
				let result = if (n1 < n2) then LTrue else LFalse in
				DynArray.set p_formulae n result; f symb_state
		   | _, _ -> go_through_pfs rest (n + 1)
		  )

		| LLessEq (le1, le2) ->
		  (match le1, le2 with
		   | LLit (Integer n1), LLit (Integer n2) ->
				let result = if (n1 <= n2) then LTrue else LFalse in
				DynArray.set p_formulae n result; f symb_state
		   | LLit (Integer n1), LLit (Num n2) ->
				let result = if (float_of_int n1 <= n2) then LTrue else LFalse in
				DynArray.set p_formulae n result; f symb_state
		   | LLit (Num n1), LLit (Integer n2) ->
				let result = if (n1 <= float_of_int n2) then LTrue else LFalse in
				DynArray.set p_formulae n result; f symb_state
		   | LLit (Num n1), LLit (Num n2) ->
				let result = if (n1 <= n2) then LTrue else LFalse in
				DynArray.set p_formulae n result; f symb_state
		   | _, _ -> go_through_pfs rest (n + 1)
		  )

		(* These shouldn't even be here *)
		| LPointsTo	(_, _, _) -> raise (Failure "Heap cell assertion in pure formulae.")
		| LEmp -> raise (Failure "Empty heap assertion in pure formulae.")
		| LPred	(_, _) -> raise (Failure "Predicate in pure formulae.")
		| LTypes _ -> raise (Failure "Types in pure formulae.")

		| LAnd  (a1, a2)
		| LStar	(a1, a2) -> DynArray.set p_formulae n a1; DynArray.add p_formulae a2; f symb_state

		| LNot la ->
		  (match la with
		   | LEq (le1, le2) ->
		     (match le1, le2 with
		      | LLit l1, LLit l2 ->
			   	 (match (l1 = l2) with
				  | true -> pfs_false "Two literals are equal."
				  | false -> DynArray.delete p_formulae n; f symb_state)
			  | _, _ -> go_through_pfs rest (n + 1))
		   | _ -> go_through_pfs rest (n + 1)) (* FOR NOW! *)
		| LEq (le1, le2) -> (match (le1 = le2) with
		  | true ->
		  	  DynArray.delete p_formulae n;
		      f symb_state
		  | false -> (match le1, le2 with
			(* Literals *)
			| LLit l1, LLit l2 ->
			  (match (l1 = l2) with
			   | true -> DynArray.delete p_formulae n; f symb_state
			   | false -> pfs_false "Two literals are not equal.")
			  (* Variable and a literal: substitute in heap, substitute in store, substitute in pfs, kill in gamma *)
 			| LVar var, _ when (isSubstitutable le2) ->
			  (* print_debug (Printf.sprintf "Var and substitutable: %s and %s" var (JSIL_Print.string_of_logic_expression le2 false)); *)
 			  (* create substitution *)
 			  let subst = Hashtbl.create 1 in
 		      Hashtbl.add subst var le2;
 			  DynArray.delete p_formulae n;
 			  (* understand deletion *)
 			  let it_stays = if (save_all_lvars) then true else (String.get var 0 = '#') in
 		      let new_to_add =
 			  (match it_stays with
 			   | false ->
 			       while (Hashtbl.mem gamma var) do Hashtbl.remove gamma var done;
 				   to_add
 			   | true ->
 				 (* print_debug (Printf.sprintf "Adding: (%s, %s)\n" var (JSIL_Print.string_of_logic_expression le2 false)); *)
 			     ((var, le2) :: to_add)
 			   ) in
 			   let symb_state = symb_state_substitution symb_state subst true in
			   let other_pfs = pf_substitution other_pfs subst true in
 			   let to_add = List.map (fun (var, le) -> (var, lexpr_substitution le subst true)) to_add in
 			   aggressively_simplify new_to_add other_pfs save_all_lvars symb_state

			| LNone, l2 when (not (l2 = LNone)) -> pfs_false "None and not none."

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
			(* LEList and a LstCons *)
			| LEList ll1, LBinOp (le, LstCons, ll2)
			| LBinOp (le, LstCons, ll2), LEList ll1 ->
			  let len1 = List.length ll1 in
			  if (len1 = 0) then pfs_false "Lists are not of the same length."
			  else
			  begin
				DynArray.delete p_formulae n;
				DynArray.add p_formulae (LEq (List.hd ll1, le));
				DynArray.add p_formulae (LEq (LEList (List.tl ll1), ll2));
				f symb_state
			  end
			(* LitList and a LstCons *)
			| LLit (LList ll1), LBinOp (le, LstCons, ll2)
			| LBinOp (le, LstCons, ll2), LLit (LList ll1) ->
			  let len1 = List.length ll1 in
			  if (len1 = 0) then pfs_false "Lists are not of the same length."
			  else
			  begin
				DynArray.delete p_formulae n;
				DynArray.add p_formulae (LEq (LLit (List.hd ll1), le));
				DynArray.add p_formulae (LEq (LLit (LList (List.tl ll1)), ll2));
				f symb_state
			  end
			(* Lists
			 *
			 * 2) One logical, one literal list - lengths must match, element equality, restart
			 *)
			| LEList ll1, LLit (LList ll2)
			| LLit (LList ll2), LEList ll1 ->

			  (* print_debug (Printf.sprintf "Two lists: %s and %s" (JSIL_Print.string_of_logic_expression le1 false) (JSIL_Print.string_of_logic_expression le2 false)); *)

			  let len1 = List.length ll1 in
			  let len2 = List.length ll2 in
			  if (len1 = len2) then
			  begin
				DynArray.delete p_formulae n;
				List.iter2 (fun x y -> DynArray.add p_formulae (LEq (x, LLit y))) ll1 ll2;
				f symb_state
			  end
			  else pfs_false "Lists are not of the same length."
			| LBinOp (le1, LstCons, le2), LBinOp (le3, LstCons, le4) ->
			  begin
			  	DynArray.delete p_formulae n;
				DynArray.add p_formulae (LEq (le1, le3));
				DynArray.add p_formulae (LEq (le2, le4));
				f symb_state
			  end
			(* Injective operators *)
			| LUnOp (ToStringOp, le1), LUnOp (ToStringOp, le2) ->
			  DynArray.set p_formulae n (LEq (le1, le2));
			  f symb_state
			| LStrNth (le1, le2), LStrNth (le3, le4) ->
			  if (le1 = le2) then
			  begin
				DynArray.set p_formulae n (LEq (le2, le4));
				f symb_state
			  end else go_through_pfs rest (n + 1)
			(* Whatever else *)
			| _, _ -> go_through_pfs rest (n + 1)
			)
		  )
		)
	) in

	(* print_debug (Printf.sprintf "Simplification:\n%s\nwith other:%s" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state) (JSIL_Memory_Print.string_of_shallow_p_formulae other_pfs false)); *)

	DynArray.iteri
	(fun i pf ->
	  (match pf with
	   | LEq (LVar _, LVar _) -> ()
	   | LEq (le1, LVar var) -> DynArray.set p_formulae i (LEq (LVar var, le1))
	   | _ -> ()
	  )
	) p_formulae;

	sanitise_pfs store gamma p_formulae;

	let pf_list = DynArray.to_list p_formulae in
		go_through_pfs pf_list 0

let simplify how x =
	let (result, _) = aggressively_simplify [] (DynArray.create ()) how x in result

let simplify_with_pfs how pfs = aggressively_simplify [] pfs how

let aggressively_simplify_pfs pfs gamma how =
	(* let solver = ref None in *)
		let _, _, pfs, _, _ = simplify how (LHeap.create 1, Hashtbl.create 1, (DynArray.copy pfs), (copy_gamma gamma), DynArray.create () (*, solver*)) in
			pfs

let aggressively_simplify_pfs_with_others pfs opfs gamma how =
	(* let solver = ref None in *)
		let (_, _, pfs, gamma, _), opfs = aggressively_simplify [] opfs how (LHeap.create 1, Hashtbl.create 1, (DynArray.copy pfs), (copy_gamma gamma), DynArray.create () (*, solver*)) in
			pfs, opfs, gamma

let rec simplify_existentials (exists : SS.t) lpfs (p_formulae : jsil_logic_assertion DynArray.t) (gamma : (string, jsil_type) Hashtbl.t) =

	print_time_debug ("simplify_existentials:");

	let pfs_false msg =
	     (* print_debug (msg ^ " Pure formulae false.\n"); *)
	   DynArray.clear p_formulae;
		 DynArray.add p_formulae LFalse;
		 SS.empty, lpfs, p_formulae, (Hashtbl.create 1) in

	let delete_substitute_proceed exists p_formulae gamma v n le =
		DynArray.delete p_formulae n;
		let exists = SS.remove v exists in
		while (Hashtbl.mem gamma v) do Hashtbl.remove gamma v done;
		let subst = Hashtbl.create 1 in
		Hashtbl.add subst v le;
		simplify_existentials exists lpfs (pf_substitution p_formulae subst true) gamma in

	let test_for_nonsense pfs =

		let rec test_for_nonsense_var_list var lst =
		(* print_debug (Printf.sprintf "tfni: %s, %s" (JSIL_Print.string_of_logic_expression var false) (JSIL_Print.string_of_logic_expression lst false)); *)
		(match var, lst with
		 | LVar v, LVar w -> v = w
		 | LVar _, LEList lst ->
			 List.fold_left (fun ac x -> ac || x = var) false lst
		 | LVar _, LBinOp (head, LstCons, tail) ->
			  (var = head) || (test_for_nonsense_var_list var tail)
		 | _, _ -> false
		) in

		let rec test_for_nonsense_iter pfs =
		(match pfs with
		| [] -> false
		| a :: rest -> (match a with
		  | LEq (le1, le2) ->
			(match le1, le2 with
			 | LVar _, LEList _
			 | LVar _, LBinOp (_, LstCons, _) ->
			   let is_recursive_nonsense = test_for_nonsense_var_list le1 le2 in
			   (match is_recursive_nonsense with
				| true -> true
				| false -> test_for_nonsense_iter rest)
			 | _, _ -> test_for_nonsense_iter rest)
		  | _ -> test_for_nonsense_iter rest)
		) in

	test_for_nonsense_iter pfs in

	let rec go_through_pfs (pfs : jsil_logic_assertion list) n =
	(match pfs with
	 | [] -> if (test_for_nonsense (pfs_to_list p_formulae))
			 	then pfs_false "Nonsense."
				else
			 ( print_debug (Printf.sprintf "Finished existential simplification:\n\nExistentials:\n%s\n\nPure formulae:\n%s\n\nGamma:\n%s\n\n"
		 		(String.concat ", " (SS.elements exists))
		 		(JSIL_Memory_Print.string_of_shallow_p_formulae p_formulae false)
		 		(JSIL_Memory_Print.string_of_gamma gamma));
	 		 exists, lpfs, p_formulae, gamma)
	 | pf :: rest ->
	   (match pf with
		| LEq (LVar v, le) ->
		  (match (SS.mem v exists) with
		   | false -> go_through_pfs rest (n + 1)
		   | true ->
			   (match (Hashtbl.mem gamma v) with
			    | false -> go_through_pfs rest (n + 1)
				| true ->
					let vtype = Hashtbl.find gamma v in
					(match le with
					 | LLit lit ->
					     let ltype = JSIL_Interpreter.evaluate_type_of lit in
						 (match (vtype = ltype) with
						  | false -> pfs_false "Mistypes."
						  | true -> delete_substitute_proceed exists p_formulae gamma v n le
						 )
				     | LEList _
					 | LBinOp (_, LstCons, _) ->
					     let can_we_substitute = isExistentiallySubstitutable le in
						 (match can_we_substitute with
						  | false -> go_through_pfs rest (n + 1)
						  | true -> delete_substitute_proceed exists p_formulae gamma v n le
						 )
					 | _ -> go_through_pfs rest (n + 1)
					)
			   )
		  )
		| _ -> go_through_pfs rest (n + 1)
	   )
	) in

	DynArray.iteri
	(fun i pf ->
	  (match pf with
	   | LEq (LVar _, LVar _) -> ()
	   | LEq (le1, LVar var) -> DynArray.set p_formulae i (LEq (LVar var, le1))
	   | _ -> ()
	  )
	) p_formulae;

	let p_formulae = aggressively_simplify_pfs p_formulae gamma true in

	(* print_debug (Printf.sprintf "Existential simplification:\n\nExistentials:\n%s\n\nPure formulae:\n%s\n\nGamma:\n%s\n\n"
		(String.concat ", " (SS.elements exists))
		(JSIL_Memory_Print.string_of_shallow_p_formulae p_formulae false)
		(JSIL_Memory_Print.string_of_gamma gamma)); *)

	let pf_list = DynArray.to_list p_formulae in
		go_through_pfs pf_list 0

let clean_up_stuff exists left right =
	let sleft = SA.of_list (DynArray.to_list left) in
	let i = ref 0 in
	while (!i < DynArray.length right) do
		let pf = DynArray.get right !i in
		(match (SA.mem pf sleft) with
		 | false -> i := !i + 1
		 | true -> DynArray.delete right !i
		)
	done

let simplify_implication exists lpfs rpfs gamma =
	clean_up_stuff exists lpfs rpfs;
	let lpfs, rpfs, gamma = aggressively_simplify_pfs_with_others lpfs rpfs gamma false in
	simplify_existentials exists lpfs rpfs gamma
