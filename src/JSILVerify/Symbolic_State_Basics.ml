open JSIL_Syntax
open Symbolic_State
open JSIL_Logic_Utils

(* Shorthand for printing logical expressions *)
let print_lexpr le = JSIL_Print.string_of_logic_expression le false 

(***************)
(** Shorthand **)
(***************)

let print_pfs pfs = JSIL_Memory_Print.string_of_shallow_p_formulae pfs false

(*************************************)
(** Abstract Heap functions         **)
(*************************************)



(*************************************)
(** Abstract Store functions        **)
(*************************************)

let extend_abs_store x store gamma =
	let new_l_var_name = fresh_lvar () in
	let new_l_var = LVar new_l_var_name in
	(try
		let x_type = Hashtbl.find gamma x in
		Hashtbl.add gamma new_l_var_name x_type
	with _ -> ());
	Hashtbl.add store x new_l_var;
	new_l_var


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


(*************************************)
(** Typing Environment functions    **)
(*************************************)

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

(*************************************)
(** Symbolic State functions        **)
(*************************************)

let get_preds_vars catch_pvars preds : SS.t =
	DynArray.fold_left (fun ac (_, les) ->
		let v_les = List.fold_left (fun ac e ->
			let v_e = get_expr_vars catch_pvars e in
			SS.union ac v_e) SS.empty les in
		SS.union ac v_les) SS.empty preds
	
let get_symb_state_vars catch_pvars symb_state =
	let heap, store, pfs, gamma, preds = symb_state in
	let v_h  : SS.t = heap_vars catch_pvars heap in
	let v_s  : SS.t = store_vars catch_pvars store in
	let v_pf : SS.t = get_pf_vars catch_pvars pfs in
	let v_g  : SS.t = get_gamma_vars catch_pvars gamma in
	let v_pr : SS.t = get_preds_vars catch_pvars preds in
		SS.union v_h (SS.union v_s (SS.union v_pf (SS.union v_g v_pr)))
		
let get_symb_state_vars_no_gamma catch_pvars symb_state =
	let heap, store, pfs, gamma, preds = symb_state in
	let v_h  : SS.t = heap_vars catch_pvars heap in
	let v_s  : SS.t = store_vars catch_pvars store in
	let v_pf : SS.t = get_pf_vars catch_pvars pfs in
	let v_pr : SS.t = get_preds_vars catch_pvars preds in
		SS.union v_h (SS.union v_s (SS.union v_pf v_pr))


(* IN PLACE *)

let heap_substitution_in_place (heap : symbolic_heap) (subst : substitution) =
  LHeap.iter
  	(fun loc (fv_list, def) ->
  		let s_loc =
  			(try Hashtbl.find subst loc
  				with _ ->
  					if (is_abs_loc_name loc)
  						then ALoc loc
  						else (LLit (Loc loc))) in
  		let s_loc =
  			(match s_loc with
  				| LLit (Loc loc) -> loc
  				| ALoc loc -> loc
  				| _ ->
  					raise (Failure "Heap substitution failed miserably!!!")) in
  		let s_fv_list = fv_list_substitution fv_list subst true in
  		let s_def = lexpr_substitution def subst true in
  		LHeap.replace heap s_loc (s_fv_list, s_def))
  	heap

let store_substitution_in_place store gamma subst =
	Hashtbl.iter
		(fun pvar le ->
			let s_le = lexpr_substitution le subst true in
			Hashtbl.replace store pvar s_le;
			
			let s_le_type, is_typable, _ = type_lexpr gamma s_le in
			(match s_le_type with
				| Some s_le_type -> Hashtbl.replace gamma pvar s_le_type
				| None -> ()))
		store

let pf_substitution_in_place pfs subst =
	DynArray.iteri (fun i a ->
		let s_a = JSIL_Logic_Utils.assertion_substitution a subst true in
		DynArray.set pfs i s_a) pfs

let preds_substitution_in_place preds subst =
	DynArray.iteri (fun i pred ->
		let s_pred = pred_substitution pred subst true in
		DynArray.set preds i s_pred) preds

let symb_state_substitution_in_place_no_gamma (symb_state : symbolic_state) subst =
	let heap, store, pf, gamma, preds = symb_state in
	heap_substitution_in_place heap subst;
	store_substitution store gamma subst; 
	pf_substitution_in_place pf subst;
	preds_substitution_in_place preds subst
