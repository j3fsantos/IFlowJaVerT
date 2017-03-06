open JSIL_Syntax
open Symbolic_State
open JSIL_Logic_Utils

(***************)
(** Shorthand **)
(***************)

let print_pfs pfs = JSIL_Memory_Print.string_of_shallow_p_formulae pfs false

(*************************************)
(** Abstract Heap functions         **)
(*************************************)

let is_empty_fv_list fv_list js =
	let rec loop fv_list empty_so_far =
		match fv_list with
		| [] -> empty_so_far
		| (f_name, f_val) :: rest ->
			if ((f_name = (LLit (String Js2jsil_constants.erFlagPropName))) && js) 
				then true 
				else ( if (f_val = LNone) then loop rest empty_so_far else loop rest false ) in 
	loop fv_list true

let is_symb_heap_empty (heap : symbolic_heap) (js : bool) : bool =
	LHeap.fold
		(fun loc (fv_list, def) ac -> if (not ac) then ac else is_empty_fv_list fv_list js)
		heap
		true
		
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
						raise (Failure "Heap substitution failed miserably!!!")) in
			let s_fv_list = fv_list_substitution fv_list subst partial in
			let s_def = lexpr_substitution def subst partial in
			LHeap.add new_heap s_loc (s_fv_list, s_def))
		heap;
	new_heap

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
							| Some s_le_type -> Hashtbl.replace gamma pvar s_le_type
							| None -> ());
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
	let vars, les = 
		List.fold_left 
			(fun (vars, les) v ->
				if (Hashtbl.mem store v) 
					then (v :: vars), ((Hashtbl.find store v) :: les) 
					else vars, les)
			([], []) 
			vars in
	init_store vars les

let merge_stores (store_l : symbolic_store) (store_r : symbolic_store) =
	Hashtbl.iter
		(fun var expr ->
			if (not (Hashtbl.mem store_l var))
				then Hashtbl.add store_l var expr)
		store_r

let check_store store gamma =

	let placeholder pvar le target_type =
		if (Hashtbl.mem gamma pvar) then
		begin
		  let _type = Hashtbl.find gamma pvar in
		  	(target_type = _type)
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
							let new_lvar = Symbolic_State.fresh_lvar () in
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
	with (Failure msg) -> print_endline (Printf.sprintf "%s" msg); false

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
	

let simple_subtract_pred preds pred_name = 
	let pred_asses = DynArray.to_list preds in 
	let rec loop pred_asses cur = 
		(match pred_asses with 
		| [] -> None
		| (cur_pred_name, les) :: rest -> 
			if (cur_pred_name = pred_name) 
			then Some (cur, les)
			else loop rest (cur + 1)) in 
	match (loop pred_asses 0) with 
	| None -> None
	| Some (cur, les) -> (DynArray.delete preds cur); Some (pred_name, les)
		

(*************************************)
(** Symbolic State functions        **)
(*************************************)

let init_symb_state () : symbolic_state =
	(* Heap, Store, Pure Formula, Gamma, Preds *)
	(LHeap.create 1, Hashtbl.create 1, DynArray.create (), Hashtbl.create 1, DynArray.create ())

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

(* 
let is_empty_symb_state symb_state =
	(is_symb_heap_empty (get_heap symb_state)) && (is_preds_empty (get_preds symb_state)) *)


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


(**
   @arg catch_pvars boolean - if true, the procedure returns logical variables AND program variables. 
	      otherwise it only returns logical variables 
	 @ret a list containing all the variables in symb_state   
*)
let get_symb_state_vars_as_list (catch_pvars : bool) (symb_state : symbolic_state) =
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
		(print_pfs pfs_old)
		(print_pfs pfs))

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
     (fun ac x -> ac && isExistentiallySubstitutable x) true les
 | LBinOp (le, LstCons, les) -> isExistentiallySubstitutable le && isExistentiallySubstitutable les
 | _ -> false
)

let get_lvars_pfs pfs =
	List.fold_left
		(fun lvars pf -> 
			let lvs = get_assertion_lvars pf in
				SS.union lvars lvs)
		SS.empty (DynArray.to_list pfs)
	
let filter_gamma_pfs pfs gamma = 
	let pfs_vars = get_lvars_pfs pfs in
	Hashtbl.filter_map_inplace 
		(fun k v -> if (SS.mem k pfs_vars) then Some v else None) 
		gamma
	
(*
	SIMPLIFICATION AND MORE INFORMATION
	===================================

*)

let rec aggressively_simplify (to_add : (string * jsil_logic_expr) list) other_pfs save_all_lvars (symb_state : symbolic_state) : (symbolic_state * jsil_logic_assertion DynArray.t * (string * jsil_logic_expr) list) =

	let f = aggressively_simplify to_add other_pfs save_all_lvars in

	(* Break down the state into components *)
	let heap, store, p_formulae, gamma, preds (*, _ *) = symb_state in

	(* When we know the formulae are false, set the implication to false -> true *)
	let pfs_false msg =
		print_debug (msg ^ " Pure formulae false.\n");
		DynArray.clear p_formulae;
		DynArray.add p_formulae LFalse;
		DynArray.clear other_pfs;
		symb_state, other_pfs, [] in
	
	let perform_substitution var lexpr n chantay = 
	let subst = Hashtbl.create 1 in
		Hashtbl.add subst var lexpr;
		DynArray.delete p_formulae n;
		let new_to_add =
		  (match chantay with
		   | false ->
			   while (Hashtbl.mem gamma var) do Hashtbl.remove gamma var done;
			   to_add
		   | true -> ((var, lexpr) :: to_add)) in
		let symb_state = symb_state_substitution symb_state subst true in
		let other_pfs = pf_substitution other_pfs subst true in
		aggressively_simplify new_to_add other_pfs save_all_lvars symb_state in

	(* Main recursive function *)
	let rec go_through_pfs (pfs : jsil_logic_assertion list) n =
		(match pfs with
		| [] ->
			List.iter (fun (x, y) -> DynArray.add p_formulae (LEq (LVar x, y))) to_add;
			symb_state, other_pfs, to_add
		| pf :: rest ->
			(match pf with
			(* If we have true in the pfs, we delete it and restart *)
			| LTrue -> DynArray.delete p_formulae n; go_through_pfs rest n
			(* If we have false in the pfs, everything is false and we stop *)
			| LFalse -> pfs_false ""
			(* Getting rid of disequalities that we know hold due to typing *)
			| LNot (LEq (le1, le2)) ->
				let te1, _, _ = type_lexpr gamma le1 in
				let te2, _, _ = type_lexpr gamma le2 in
				(match te1, te2 with
				| Some t1, Some t2 ->
					(match (t1 = t2) with
					| false -> DynArray.delete p_formulae n; go_through_pfs rest n
					| true -> go_through_pfs rest (n + 1))
				| _, _ -> go_through_pfs rest (n + 1))
			| LEq (le1, le2) ->
				(match le1, le2 with
				(* Obvious falsity *)
				| ALoc loc, LLit l
				| LLit l, ALoc loc ->
					(match l with
					 | Loc _ -> go_through_pfs rest (n + 1)
					 | _ -> pfs_false (Printf.sprintf "ALoc and not-a-loc: %s, %s" loc (JSIL_Print.string_of_literal l false)))
				(* VARIABLES *)
				| LVar v1, LVar v2 ->
					let does_this_work = 
						(match (Hashtbl.mem gamma v1, Hashtbl.mem gamma v2) with
						| true, true -> 
							let t1 = Hashtbl.find gamma v1 in
							let t2 = Hashtbl.find gamma v2 in
								(t1 = t2)
						| true, false ->
							let t1 = Hashtbl.find gamma v1 in
								Hashtbl.add gamma v2 t1;
								true
						| false, true ->
							let t2 = Hashtbl.find gamma v2 in
								Hashtbl.add gamma v1 t2;
								true
						| _, _ -> true) in
					if does_this_work 
						then go_through_pfs rest (n + 1)
						else pfs_false "Nasty type mismatch"
				| LVar v, LLit lit -> 
					let does_this_work = 
						let tl = JSIL_Interpreter.evaluate_type_of lit in
						(match Hashtbl.mem gamma v with
						| true -> 
							let t1 = Hashtbl.find gamma v in
								(t1 = tl)
						| false -> Hashtbl.add gamma v tl; true) in
					if does_this_work 
						then perform_substitution v le2 n (save_all_lvars || String.get v 0 = '#')
						else pfs_false "Nasty type mismatch: var -> lit"
				| LVar v, _ when (isSubstitutable le2) ->
					perform_substitution v le2 n (save_all_lvars || String.get v 0 = '#')
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
				  if (ll1 = []) then pfs_false "Lists are not of the same length."
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
				  if (ll1 = []) then pfs_false "Lists are not of the same length."
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
				(* More falsity *)
				| LEList _, LLit _
				| LLit _, LEList _ 
				| LBinOp (_, LstCons, _), LLit _
				| LLit _ , LBinOp (_, LstCons, _) -> pfs_false "List and not-a-list"
				
				(* Otherwise, continue *)
				| _, _ -> go_through_pfs rest (n + 1))
			
			(* I don't know how these could get here, but let's assume they can... *)
			| LAnd  (a1, a2)
			| LStar	(a1, a2) -> DynArray.set p_formulae n a1; DynArray.add p_formulae a2; f symb_state
			
			(* Otherwise, continue *)
			| _ -> go_through_pfs rest (n + 1)
			)
		) in

	(* *******************
	 *  ACTUAL PROCESSING
	 * ******************* *) 

	(* Bring lvars to the left side of the equality or not-equality *)
	DynArray.iteri
	(fun i pf ->
	  (match pf with
	   (* Move lvars with # to the left *)
	   | LEq (LVar v1, LVar v2) when (String.get v1 0 = '_' && String.get v2 0 = '#') -> DynArray.set p_formulae i (LEq (LVar v2, LVar v1))
	   (* Don't do anything if the left lvar is with _ or with # *)
	   | LEq (LVar v1, _)       when (String.get v1 0 = '_' || String.get v1 0 = '#') -> ()
	   (* Otherwise, swap *)
	   | LEq (le1, LVar var) -> DynArray.set p_formulae i (LEq (LVar var, le1))
	   (* Move lvars with # to the left *)
	   | LNot (LEq (LVar v1, LVar v2)) when (String.get v1 0 = '_' && String.get v2 0 = '#') -> DynArray.set p_formulae i (LNot (LEq (LVar v2, LVar v1)))
	   (* Don't do anything if the left lvar is with _ or with # *)
	   | LNot (LEq (LVar v1, _))       when (String.get v1 0 = '_' || String.get v1 0 = '#') -> ()
	   (* Otherwise, swap *)
	   | LNot (LEq (le1, LVar var)) -> DynArray.set p_formulae i (LNot (LEq (LVar var, le1)))
	   | _ -> ()
	  )
	) p_formulae;

	(* Sanitise *)
	sanitise_pfs store gamma p_formulae;

	(* Process *)
	let pf_list = DynArray.to_list p_formulae in
		go_through_pfs pf_list 0
		

let simplify how x =
	let (result, _, _) = aggressively_simplify [] (DynArray.create ()) how x in result

let simplify_with_subst how x = 
	let (result, _, subst) = aggressively_simplify [] (DynArray.create ()) how x in result, subst

let simplify_with_pfs how pfs = aggressively_simplify [] pfs how

let aggressively_simplify_pfs pfs gamma how =
	(* let solver = ref None in *)
		let _, _, pfs, _, _ = simplify how (LHeap.create 1, Hashtbl.create 1, (DynArray.copy pfs), (copy_gamma gamma), DynArray.create () (*, solver*)) in
			pfs

let aggressively_simplify_pfs_with_others pfs opfs gamma how =
	(* let solver = ref None in *)
		let (_, _, pfs, gamma, _), opfs, _ = aggressively_simplify [] opfs how (LHeap.create 1, Hashtbl.create 1, (DynArray.copy pfs), (copy_gamma gamma), DynArray.create () (*, solver*)) in
			pfs, opfs, gamma
	
(* *********************** *
 * ULTIMATE SIMPLIFICATION *
 * *********************** *)

let rec understand_types exists pf_list gamma : bool = 
	let f = understand_types exists in
	(match pf_list with
	| [] -> true
	| (pf, from_where) :: rest ->
	 	(match pf with
		| LTrue | LFalse | LEmp | LNot _ -> f rest gamma
		| LPointsTo	(_, _, _) -> raise (Failure "Heap cell assertion in pure formulae.")
		| LEmp -> raise (Failure "Empty heap assertion in pure formulae.")
		| LPred	(_, _) -> raise (Failure "Predicate in pure formulae.")
		| LTypes _ -> raise (Failure "Types in pure formulae.")
		| LEmptyFields (_, _) -> raise (Failure "EmptyFields in pure formulae.")

		| LEq (le1, le2) -> 
			(* Get the types, if possible *)
			let te1, _, _ = type_lexpr gamma le1 in
			let te2, _, _ = type_lexpr gamma le2 in
			(* Understand if there's enough information to proceed *)
			let proceed = (match te1, te2 with
			| Some t1, Some t2 -> Some (t1 = t2)
			| None, None -> None
			| _, _ -> Some true) in
			(match proceed with
			| None -> f rest gamma
			| Some false -> false
			| Some true -> (* Check for variables *)
				(match le1, le2 with
				| LVar x, LVar y ->
					(* print_debug (Printf.sprintf "Checking: (%s, %s) vs %s" x  from_where y); *)
					(match te1, te2 with
					| Some t1, None ->
						if ((from_where = "l") || ((from_where = "r") && (SS.mem y exists))) 
						then (print_debug (Printf.sprintf "Added (%s, %s) to gamma given %s and %s" 
							y (JSIL_Print.string_of_type t1)
							(String.concat "\n" (List.map (fun (x, y) -> Printf.sprintf "(%s, %s)" (JSIL_Print.string_of_logic_assertion x false) y) pf_list))
							(JSIL_Memory_Print.string_of_gamma gamma)); 
							Hashtbl.add gamma y t1); 
						f rest gamma
					| None, Some t2 ->
							if ((from_where = "l") || ((from_where = "r") && (SS.mem x exists))) 
							then (print_debug (Printf.sprintf "Added (%s, %s) to gamma given %s and %s" 
								x (JSIL_Print.string_of_type t2)
								(String.concat "\n" (List.map (fun (x, y) -> Printf.sprintf "(%s, %s)" (JSIL_Print.string_of_logic_assertion x false) y) pf_list))
								(JSIL_Memory_Print.string_of_gamma gamma)); 
								Hashtbl.add gamma x t2); 
							f rest gamma 
					| Some t1, Some t2 -> f rest gamma
					| None, None -> raise (Failure "Impossible branch."))
				| LVar x, le
				| le, LVar x ->
					(* print_debug (Printf.sprintf "Checking: (%s, %s) vs %s" x from_where (JSIL_Print.string_of_logic_expression le false)); *)
					let tx = gamma_get_type gamma x in
					let te, _, _ = type_lexpr gamma le in
					(match te with
					| None -> f rest gamma
					| Some te ->
						(match tx with
						| None -> 
								if ((from_where = "l") || ((from_where = "r") && (SS.mem x exists)))
								then (
									print_debug (Printf.sprintf "Added (%s, %s) to gamma given %s and %s" 
									x (JSIL_Print.string_of_type te)
									(String.concat "\n" (List.map (fun (x, y) -> Printf.sprintf "(%s, %s)" (JSIL_Print.string_of_logic_assertion x false) y) pf_list))
									(JSIL_Memory_Print.string_of_gamma gamma)); 
									Hashtbl.add gamma x te); 
								f rest gamma
						| Some tx -> f rest gamma))
					| _, _ -> f rest gamma))
		| _ -> f rest gamma))

let rec simplify_for_your_legacy exists others (symb_state : symbolic_state) : symbolic_state * jsil_logic_assertion DynArray.t = 

	(* Gamma-check *)
	let symb_state, others = Hashtbl.fold (fun v t (ac, others) -> 
		let (heap, store, p_formulae, gamma, preds (*, _ *)) = ac in
		let lexpr = 
		(match t with
			| UndefinedType -> Some (LLit Undefined)
			| NullType -> Some (LLit Null)
			| EmptyType -> Some (LLit Empty)
			| NoneType -> Some LNone
			| _ -> None) in
		(match lexpr with
		| Some lexpr ->
			let subst = Hashtbl.create 1 in
			Hashtbl.add subst v lexpr;
			while (Hashtbl.mem gamma v) do Hashtbl.remove gamma v done;
			(symb_state_substitution (heap, store, p_formulae, gamma, preds) subst true, pf_substitution others subst true)
		| None -> (ac, others))) (copy_gamma (get_gamma symb_state)) (symb_state, others) in

	let f  = simplify_for_your_legacy exists in
	let fo = simplify_for_your_legacy exists others in

	let heap, store, p_formulae, gamma, preds (*, _ *) = symb_state in
	
	let pfs_false msg =
		print_debug (msg ^ " Pure formulae false.\n");
		DynArray.clear p_formulae;
		DynArray.add p_formulae LFalse;
		symb_state, DynArray.create () in
		 
	let perform_substitution var lexpr n = 
		let subst = Hashtbl.create 1 in
			Hashtbl.add subst var lexpr;
			DynArray.delete p_formulae n;
			while (Hashtbl.mem gamma var) do Hashtbl.remove gamma var done;
			let symb_state = symb_state_substitution symb_state subst true in
			let others = pf_substitution others subst true in
			f others symb_state in
		 
	let rec go_through_pfs (pfs : jsil_logic_assertion list) n =
	(match pfs with
	 | [] -> symb_state, others
     | pf :: rest ->
	 	(match pf with
			(* If we have true in the pfs, we delete it and restart *)
			| LTrue -> DynArray.delete p_formulae n; go_through_pfs rest n
			
			(* If we have false in the pfs, everything is false and we stop *)
			| LFalse -> pfs_false ""
			
			(* We can reduce < if both are numbers *)
			| LLess	(le1, le2) ->
			  (match le1, le2 with
			   | LLit (Num n1), LLit (Num n2) ->
					let result = if (n1 < n2) then LTrue else LFalse in
					DynArray.set p_formulae n result; fo symb_state
			   | _, _ -> go_through_pfs rest (n + 1)
			  )

			(* Same for <= *)
			| LLessEq (le1, le2) ->
			  (match le1, le2 with
			   | LLit (Num n1), LLit (Num n2) ->
					let result = if (n1 <= n2) then LTrue else LFalse in
					DynArray.set p_formulae n result; fo symb_state
			   | _, _ -> go_through_pfs rest (n + 1)
			  )

			(* These shouldn't even be here *)
			| LPointsTo	(_, _, _) -> raise (Failure "Heap cell assertion in pure formulae.")
			| LEmp -> raise (Failure "Empty heap assertion in pure formulae.")
			| LPred	(_, _) -> raise (Failure "Predicate in pure formulae.")
			| LTypes _ -> raise (Failure "Types in pure formulae.")
			| LEmptyFields (_, _) -> raise (Failure "EmptyFields in pure formulae.")

			(* I don't know how these could get here, but let's assume they can... *)
			| LAnd  (a1, a2)
			| LStar	(a1, a2) -> DynArray.set p_formulae n a1; DynArray.add p_formulae a2; fo symb_state

			(* Getting rid of disequalities that we know hold due to typing *)
			| LNot (LEq (le1, le2)) ->
				let te1, _, _ = type_lexpr gamma le1 in
				let te2, _, _ = type_lexpr gamma le2 in
				(match te1, te2 with
				| Some t1, Some t2 ->
					(match (t1 = t2) with
					| false -> DynArray.delete p_formulae n; go_through_pfs rest n
					| true -> go_through_pfs rest (n + 1))
				| _, _ -> go_through_pfs rest (n + 1))

			| LEq (le1, le2) ->
				(match le1, le2 with
				(* VARIABLES *)
				| LVar v, le 
				| le, LVar v -> perform_substitution v le n
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
					fo symb_state
				  end
				  else pfs_false "Lists are not of the same length."
				(* LEList and a LstCons *)
				| LEList ll1, LBinOp (le, LstCons, ll2)
				| LBinOp (le, LstCons, ll2), LEList ll1 ->
				  if (ll1 = []) then pfs_false "Lists are not of the same length."
				  else
				  begin
					DynArray.delete p_formulae n;
					DynArray.add p_formulae (LEq (List.hd ll1, le));
					DynArray.add p_formulae (LEq (LEList (List.tl ll1), ll2));
					fo symb_state
				  end
				(* LitList and a LstCons *)
				| LLit (LList ll1), LBinOp (le, LstCons, ll2)
				| LBinOp (le, LstCons, ll2), LLit (LList ll1) ->
				  if (ll1 = []) then pfs_false "Lists are not of the same length."
				  else
				  begin
					DynArray.delete p_formulae n;
					DynArray.add p_formulae (LEq (LLit (List.hd ll1), le));
					DynArray.add p_formulae (LEq (LLit (LList (List.tl ll1)), ll2));
					fo symb_state
				  end
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
					fo symb_state
				  end
				  else pfs_false "Lists are not of the same length."
				| LBinOp (le1, LstCons, le2), LBinOp (le3, LstCons, le4) ->
				  begin
					DynArray.delete p_formulae n;
					DynArray.add p_formulae (LEq (le1, le3));
					DynArray.add p_formulae (LEq (le2, le4));
					fo symb_state
				  end
				| _, _ -> go_through_pfs rest (n + 1))
			| _ -> go_through_pfs rest (n + 1))
	) in
	
	(*
	| LLess			    of jsil_logic_expr * jsil_logic_expr                   (** Expression less-than for numbers *)
	| LLessEq		    of jsil_logic_expr * jsil_logic_expr                   (** Expression less-than-or-equal for numbers *)   
	| LStrLess	    of jsil_logic_expr * jsil_logic_expr                   (** Expression less-than for strings *) *)

	(* *******************
	 *  ACTUAL PROCESSING
	 * ******************* *) 

	(* Bring lvars to the left side of the equality or not-equality *)
	DynArray.iteri
	(fun i pf ->
	  (match pf with
	   (* Move lvars with # to the left *)
	   | LEq (LVar v1, LVar v2) when (String.get v1 0 = '_' && String.get v2 0 = '#') -> DynArray.set p_formulae i (LEq (LVar v2, LVar v1))
	   (* Don't do anything if the left lvar is with _ or with # *)
	   | LEq (LVar v1, _)       when (String.get v1 0 = '_' || String.get v1 0 = '#') -> ()
	   (* Otherwise, swap *)
	   | LEq (le1, LVar var) -> DynArray.set p_formulae i (LEq (LVar var, le1))
	   (* Move lvars with # to the left *)
	   | LNot (LEq (LVar v1, LVar v2)) when (String.get v1 0 = '_' && String.get v2 0 = '#') -> DynArray.set p_formulae i (LNot (LEq (LVar v2, LVar v1)))
	   (* Don't do anything if the left lvar is with _ or with # *)
	   | LNot (LEq (LVar v1, _))       when (String.get v1 0 = '_' || String.get v1 0 = '#') -> ()
	   (* Otherwise, swap *)
	   | LNot (LEq (le1, LVar var)) -> DynArray.set p_formulae i (LNot (LEq (LVar var, le1)))
	   | _ -> ()
	  )
	) p_formulae;

	(* Sanitise *)
	sanitise_pfs store gamma p_formulae;

	let pf_list = DynArray.to_list p_formulae in
	let others_list = DynArray.to_list others in
	(* print_debug (Printf.sprintf "Typing pfs with others: %s%s" (JSIL_Memory_Print.string_of_shallow_p_formulae p_formulae false) (JSIL_Memory_Print.string_of_shallow_p_formulae others false)); *)
		let types_ok = understand_types exists ((List.map (fun x -> (x, "l")) pf_list) @ (List.map (fun x -> (x, "r")) others_list)) gamma in
		(match types_ok with
		| true -> go_through_pfs pf_list 0  
		| false -> pfs_false "Nasty type mismatch.")

let simplify_for_your_legacy_pfs pfs gamma =
	(* let solver = ref None in *)
		let (_, _, pfs, gamma, _), _ = simplify_for_your_legacy (SS.empty) (DynArray.create()) (LHeap.create 1, Hashtbl.create 1, (DynArray.copy pfs), (copy_gamma gamma), DynArray.create () (*, solver*)) in
			pfs, gamma
			
let simplify_for_your_legacy_pfs_with_exists_and_others exists pfs others gamma =
	(* let solver = ref None in *)
		let (_, _, pfs, gamma, _), others = simplify_for_your_legacy exists others (LHeap.create 1, Hashtbl.create 1, (DynArray.copy pfs), (copy_gamma gamma), DynArray.create () (*, solver*)) in
			pfs, others, gamma
			
let rec simplify_existentials (exists : SS.t) lpfs (p_formulae : jsil_logic_assertion DynArray.t) (gamma : (string, jsil_type) Hashtbl.t) =

	print_time_debug ("simplify_existentials:");
	
	let p_formulae = aggressively_simplify_pfs p_formulae gamma true in

	let pfs_false msg =
		print_debug (msg ^ " Pure formulae false.\n");
		DynArray.clear p_formulae;
		DynArray.add p_formulae LFalse;
		SS.empty, lpfs, p_formulae, (Hashtbl.create 1) in

	let delete_substitute_proceed exists p_formulae gamma v n le =
		print_debug (Printf.sprintf "Deleting the formula \n%s\n and substituting the variable %s for %s." 
			(JSIL_Print.string_of_logic_assertion (DynArray.get p_formulae n) false) 
			v (JSIL_Print.string_of_logic_expression le false));
		DynArray.delete p_formulae n;
		let exists = SS.remove v exists in
		while (Hashtbl.mem gamma v) do Hashtbl.remove gamma v done;
		let subst = Hashtbl.create 1 in
		Hashtbl.add subst v le;
		simplify_existentials exists lpfs (pf_substitution p_formulae subst true) gamma in

	let test_for_nonsense pfs =

		let rec test_for_nonsense_var_list var lst =
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
			 (let pf_list = DynArray.to_list p_formulae in
				let types_ok = understand_types exists (List.map (fun x -> (x, "r")) pf_list) gamma in
				(match types_ok with
				| false -> pfs_false "Nasty type mismatch."
				| true -> 
					print_debug (Printf.sprintf "Finished existential simplification:\n\nExistentials:\n%s\n\nPure formulae:\n%s\n\nGamma:\n%s\n\n"
			 		(String.concat ", " (SS.elements exists))
			 		(print_pfs p_formulae)
			 		(JSIL_Memory_Print.string_of_gamma gamma)); 
		 		 	exists, lpfs, p_formulae, gamma))
	 | pf :: rest ->
	   (match pf with
	    | LEq (LLit l1, LLit l2) ->
	    	if (l1 = l2) 
	    		then (DynArray.delete p_formulae n; go_through_pfs rest n)
	    		else pfs_false "Literals."
		| LEq (LVar x, LVar y) ->
			let mx = SS.mem x exists in
			let my = SS.mem y exists in
			(match mx, my with
			| false, false -> go_through_pfs rest (n + 1)
			| false, true  -> delete_substitute_proceed exists p_formulae gamma y n (LVar x) 
			| true,  _ -> delete_substitute_proceed exists p_formulae gamma x n (LVar y))
		| LEq (LVar v, le) 
		| LEq (le, LVar v) ->
		   (match (SS.mem v exists) with
		   | false -> go_through_pfs rest (n + 1)
		   | true ->
		       (* Why? - if not in gamma and we can type the thing on the right, add to gamma *)
			   (match (Hashtbl.mem gamma v) with
			    | false -> 
					(match le with
						 | LLit lit ->
							 let ltype = JSIL_Interpreter.evaluate_type_of lit in
							 Hashtbl.replace gamma v ltype;
							 delete_substitute_proceed exists p_formulae gamma v n le
						 | ALoc _ ->
						 	 Hashtbl.replace gamma v ObjectType;
							 delete_substitute_proceed exists p_formulae gamma v n le
						 | LEList _
						 | LBinOp (_, LstCons, _) ->
						 	 Hashtbl.replace gamma v ListType;
							 let can_we_substitute = isExistentiallySubstitutable le in
							 (match can_we_substitute with
							  | false -> go_through_pfs rest (n + 1)
							  | true -> delete_substitute_proceed exists p_formulae gamma v n le
							 )
						 | _ -> go_through_pfs rest (n + 1))
				| true ->
					let vtype = Hashtbl.find gamma v in
					(match le with
					 | LLit lit ->
					     let ltype = JSIL_Interpreter.evaluate_type_of lit in
						 (match (vtype = ltype) with
						  | false -> pfs_false "Mistypes."
						  | true -> delete_substitute_proceed exists p_formulae gamma v n le
						 )
					 | ALoc _ -> 
					 	(match (vtype = ObjectType) with
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

	let pf_list = DynArray.to_list p_formulae in
		go_through_pfs pf_list 0 



(* *********** *)
(*   CLEANUP   *)
(* *********** *)
let clean_up_stuff exists left right =
	let sleft = SA.of_list (DynArray.to_list left) in
	let i = ref 0 in
	
	while (!i < DynArray.length right) do
		let pf = DynArray.get right !i in
		let pf_sym pf = (match pf with
			| LEq (e1, e2) -> SA.mem (LEq (e2, e1)) sleft
			| LNot (LEq (e1, e2)) -> SA.mem (LNot (LEq (e2, e1))) sleft
			| _ -> false) in
		(match ((SA.mem pf sleft) || (pf_sym pf)) with
		| false -> 
			let npf = (match pf with
					| LNot pf -> pf
					| _ -> LNot pf) in
			 	(match ((SA.mem npf sleft) || (pf_sym npf)) with
				| false -> i := !i + 1
				| true -> 
						DynArray.clear left; DynArray.clear right;
						DynArray.add left LFalse)
		 | true -> DynArray.delete right !i
		)
	done

let simplify_implication exists lpfs rpfs gamma =
	let lpfs, rpfs, gamma = simplify_for_your_legacy_pfs_with_exists_and_others exists lpfs rpfs gamma in
	print_debug (Printf.sprintf "In between:\nExistentials:\n%s\nLeft:\n%s\nRight:\n%s\nGamma:\n%s\n"
   (String.concat ", " (SS.elements exists))
   (JSIL_Memory_Print.string_of_shallow_p_formulae lpfs false)
   (JSIL_Memory_Print.string_of_shallow_p_formulae rpfs false)
   (JSIL_Memory_Print.string_of_gamma gamma));
	sanitise_pfs_no_store gamma rpfs;
	let exists, lpfs, rpfs, gamma = simplify_existentials exists lpfs rpfs gamma in
	clean_up_stuff exists lpfs rpfs;
	exists, lpfs, rpfs, gamma
	

(*************************************************)
(** Symbolic state simplification  - top level  **)
(*************************************************)

let simplify_symbolic_state symb_state = 
	let pfs = get_pf_list symb_state in 
	let gamma = get_gamma symb_state in 
	let types_ok = understand_types SS.empty (List.map (fun x -> (x, "l")) pfs) gamma in
	match types_ok with
		| true -> symb_state
		| false -> raise (Failure "INCONSISTENT STATE") 	
