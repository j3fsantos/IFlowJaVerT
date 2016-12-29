open JSIL_Syntax
open JSIL_Memory_Model
open JSIL_Logic_Utils
open Symbolic_State_Basics

let verbose = ref true

let proto_f = "@proto"

(***************************)
(** Symbolic Execution    **)
(***************************)
let rec symb_evaluate_expr (expr : jsil_expr) store gamma pure_formulae =
	match expr with
	| Literal lit -> LLit lit

	| Var x ->
		let x_val = store_get_var_val store x in
		(match x_val with
		| Some x_val -> x_val
		| None       -> extend_abs_store x store gamma)

	| BinOp (e1, op, e2) ->
		let nle1 = symb_evaluate_expr e1 store gamma pure_formulae in
		let nle2 = symb_evaluate_expr e2 store gamma pure_formulae in
		(match nle1, nle2 with
		| LLit l1, LLit l2 ->
			let l = JSIL_Interpreter.evaluate_binop op (Literal l1) (Literal l2) (Hashtbl.create 1) in
			LLit l
		| _, _ ->
			(match op with
			| Equal ->
				let t1, _, _ = JSIL_Logic_Utils.type_lexpr gamma nle1 in
				let t2, _, _ = JSIL_Logic_Utils.type_lexpr gamma nle2 in
				(match t1, t2 with
				| Some t1, Some t2 -> if (not (t1 = t2)) then (LLit (Bool false)) else LBinOp (nle1, op, nle2)
				| _, _             -> LBinOp (nle1, op, nle2))
			| _ -> LBinOp (nle1, op, nle2)))

	| UnOp (op, e) ->
		let nle = symb_evaluate_expr e store gamma pure_formulae in
		(match op with
		 | Cdr ->
		 	 let nle = find_me_Im_a_list store pure_formulae nle in
			 (match nle with
				 | LLit (LList list) ->
				 	(match list with
					 | [] -> raise (Failure "Cdr doesn't exist.")
					 | _ :: list -> LLit (LList list))
				 | LEList list ->
				 	(match list with
					 | [] -> raise (Failure "Cdr doesn't exist.")
					 | _ :: list -> LEList list)
				 | LBinOp (el, LstCons, llist) -> llist
				 | _ -> LUnOp (op, nle))
		 | LstLen ->
		 	let nle = find_me_Im_a_list store pure_formulae nle in
		 	(match nle with
				| LLit (LList list) -> LLit (Integer (List.length list))
				| LEList list -> LLit (Integer (List.length list))
				| LBinOp (el, LstCons, llist) ->
					(match llist with
					  | LLit (LList list) -> LLit (Integer (1 + List.length list))
					  | LEList list -> LLit (Integer (1 + List.length list))
					  | _ -> LUnOp (op, nle))
				| _ -> LUnOp (op, nle))

		 | _ ->  (match nle with
			 	  | LLit lit -> LLit (JSIL_Interpreter.evaluate_unop op lit)
				  | _ -> LUnOp (op, nle)))

	| TypeOf (e) ->
		(** the typeof can only be removed when there are no constraints
        If there are constraints, we need to leave it there because
				the constraints cannot be ignored.                       **)
		let nle = symb_evaluate_expr e store gamma pure_formulae in
		let nle_type, _, _ = type_lexpr gamma nle in
		(match nle_type with
		| Some nle_type -> LLit (Type nle_type)
		| None          -> LTypeOf (nle))

	| EList es ->
		let les =
			List.map
				(fun e ->
					let nle = symb_evaluate_expr e store gamma pure_formulae in
					nle)
				es in
		let rec loop les lits =
			(match les with
			| [] -> true, lits
			| le :: rest ->
				(match le with
				| LLit l -> loop rest (l :: lits)
				| _ -> false, [])) in
		let all_literals, lits = loop les [] in
		let lits = List.rev lits in
		if all_literals
			then LLit (LList lits)
			else LEList les

	| LstNth (e1, e2) ->
		let list = symb_evaluate_expr e1 store gamma pure_formulae in
		let index = symb_evaluate_expr e2 store gamma pure_formulae in
		let list = find_me_Im_a_list store pure_formulae list in
		let index =
			(match index with
			| LLit (Num n) -> LLit (Integer (int_of_float n))
			| _ -> index) in
		(match index with
		 | LLit (Integer n) ->
		 	if (n < 0) then raise (Failure "List index negative.")
			else
			(match list with
				| LLit (LList list) ->
					(try (LLit (List.nth list n)) with _ ->
						raise (Failure "List index out of bounds"))
				| LEList list ->
					(try (List.nth list n) with _ ->
						raise (Failure "List index out of bounds"))
				| LBinOp (el, LstCons, llist) ->
		  			if (n = 0)
						then el
						else (match llist with
							  | LLit (LList list) -> (try (LLit (List.nth list (n - 1))) with _ ->
		  							raise (Failure "List index out of bounds"))
							  | LEList list -> (try (List.nth list (n - 1)) with _ ->
		  							raise (Failure "List index out of bounds"))
							  | _ -> LLstNth (list, index))
				| _ -> LLstNth (list, index))
		| _ -> LLstNth (list, index))

	| StrNth (e1, e2) ->
		let str = symb_evaluate_expr e1 store gamma pure_formulae in
		let index = symb_evaluate_expr e2 store gamma  pure_formulae in
		(match str, index with
		| LLit (String s), LLit (Num n) ->
			LLit (String (String.make 1 (String.get s (int_of_float n))))
		| _, _ -> LStrNth (str, index))

	| _ -> raise (Failure "not supported yet")


let safe_symb_evaluate_expr (expr : jsil_expr) store gamma pure_formulae (* solver *)  =
	let nle = symb_evaluate_expr expr store gamma pure_formulae in
	let nle_type, is_typable, constraints = type_lexpr gamma nle in
	let are_constraints_satisfied =
		(if ((List.length constraints) > 0)
			then Pure_Entailment.old_check_entailment [] (pfs_to_list pure_formulae) constraints gamma
			else true) in
	let is_typable = is_typable && are_constraints_satisfied in
	if (is_typable) then
		nle, nle_type, is_typable
	else
		(match nle with
		| LVar _ ->  nle, None, false
		| _ ->
			begin
				let gamma_str = JSIL_Memory_Print.string_of_gamma gamma in
				let pure_str = JSIL_Memory_Print.string_of_shallow_p_formulae pure_formulae false in
				let msg = Printf.sprintf "The logical expression %s is not typable in the typing enviroment: %s \n with the pure formulae %s" (JSIL_Print.string_of_logic_expression nle false) gamma_str pure_str in
				raise (Failure msg)
			end)


let symb_evaluate_bcmd bcmd (symb_state : symbolic_state) =
	let heap, store, pure_formulae, gamma, _ (*, solver *) = symb_state in
	match bcmd with
	| SSkip ->
		LLit Empty

	| SAssignment (x, e) ->
		let nle, t_le, _ = safe_symb_evaluate_expr e store gamma pure_formulae (* solver *) in
		update_abs_store store x nle;
		update_gamma gamma x t_le;
		nle

	| SNew x ->
		let new_loc = fresh_aloc () in
		Symbolic_State_Functions.update_abs_heap_default heap new_loc LNone;
		Symbolic_State_Functions.update_abs_heap heap new_loc (LLit (String proto_f)) (LLit Null) pure_formulae (* solver *) gamma;
		update_abs_store store x (ALoc new_loc);
		update_gamma gamma x (Some ObjectType);
		DynArray.add pure_formulae (LNot (LEq (ALoc new_loc, LLit (Loc Js2jsil_constants.locGlobName))));
		ALoc new_loc

	| SLookup (x, e1, e2) ->
		let ne1, t_le1, _ = safe_symb_evaluate_expr e1 store gamma pure_formulae (* solver *) in
		let ne2, t_le2, _ = safe_symb_evaluate_expr e2 store gamma pure_formulae (* solver *) in
		let l =
			(match ne1 with
			| LLit (Loc l)
			| ALoc l -> l
			| _ ->
			let ne1_str = JSIL_Print.string_of_logic_expression ne1 false  in
			let msg = Printf.sprintf "Lookup: I do not know which location %s denotes in the symbolic heap" ne1_str in
			raise (Failure msg)) in
		let ne = Symbolic_State_Functions.abs_heap_find heap l ne2 pure_formulae (* solver *) gamma in
		update_abs_store store x ne;
		ne

	| SMutation (e1, e2, e3) ->
		let ne1, t_le1, _ = safe_symb_evaluate_expr e1 store gamma pure_formulae (* solver *) in
		let ne2, t_le2, _ = safe_symb_evaluate_expr e2 store gamma pure_formulae (* solver *) in
		let ne3, _, _ = safe_symb_evaluate_expr e3 store gamma pure_formulae (* solver *) in
		(match ne1 with
		| LLit (Loc l)
		| ALoc l ->
			Symbolic_State_Functions.update_abs_heap heap l ne2 ne3 pure_formulae (* solver *) gamma
		| _ ->
			let ne1_str = JSIL_Print.string_of_logic_expression ne1 false  in
			let msg = Printf.sprintf "Mutation: I do not know which location %s denotes in the symbolic heap" ne1_str in
			raise (Failure msg));
		ne3

	| SDelete (e1, e2) ->
		let ne1, t_le1, _ = safe_symb_evaluate_expr e1 store gamma pure_formulae (* solver *) in
		let ne2, t_le2, _ = safe_symb_evaluate_expr e2 store gamma pure_formulae (* solver *) in
		let l =
			(match ne1 with
			| LLit (Loc l)
			| ALoc l -> l
			| _ ->
				let ne1_str = JSIL_Print.string_of_logic_expression ne1 false  in
				let msg = Printf.sprintf "Delete: I do not know which location %s denotes in the symbolic heap" ne1_str in
				raise (Failure msg)) in
		Symbolic_State_Functions.update_abs_heap heap l ne2 LNone pure_formulae (* solver *) gamma;
		LLit (Bool true)

	| SDeleteObj e1 ->
		let ne1, t_le1, _ = safe_symb_evaluate_expr e1 store gamma pure_formulae (* solver *) in
		let l =
			(match ne1 with
			| LLit (Loc l)
			| ALoc l -> l
			| _ ->
				let ne1_str = JSIL_Print.string_of_logic_expression ne1 false in
				let msg = Printf.sprintf "Delete: I do not know which location %s denotes in the symbolic heap" ne1_str in
				raise (Failure msg)) in
		(match (LHeap.mem heap l) with
		 | false -> raise (Failure (Printf.sprintf "Attempting to delete inexistent object: %s" (JSIL_Print.string_of_logic_expression ne1 false)))
		 | true -> LHeap.remove heap l; LLit (Bool true));

	| SHasField (x, e1, e2) ->
		let ne1, t_le1, _ = safe_symb_evaluate_expr e1 store gamma pure_formulae (* solver *) in
		let ne2, t_le2, _ = safe_symb_evaluate_expr e2 store gamma pure_formulae (* solver *) in
		match ne1 with
		| LLit (Loc l)
		| ALoc l ->
			let res = Symbolic_State_Functions.abs_heap_check_field_existence heap l ne2 pure_formulae (* solver *) gamma in
			update_gamma gamma x (Some BooleanType);
			(match res with
			| Some res ->
				let res_lit = LLit (Bool res) in
				update_abs_store store x res_lit;
				res_lit
			| None -> LUnknown)
		| _ ->
			let ne1_str = JSIL_Print.string_of_logic_expression ne1 false in
			let msg = Printf.sprintf "HasField: I do not know which location %s denotes in the symbolic heap" ne1_str in
			raise (Failure msg);

	| _ ->
		raise (Failure "not implemented yet!")



let find_and_apply_spec prog proc_name proc_specs (symb_state : symbolic_state) le_args =

	print_debug (Printf.sprintf "Entering find_and_apply_spec: %s." proc_name);

	(* create a new symb state with the abstract store in which the
	    called procedure is to be executed *)
	let proc = get_proc prog proc_name in
	let proc_args = get_proc_args proc in
	let new_store = init_store proc_args le_args in
	let symb_state_aux = symb_state_replace_store symb_state new_store in

	let compatible_pfs symb_state pat_symb_state subst =
		print_debug (Printf.sprintf "Entering compatible_pfs.");
		let pfs = get_pf symb_state in
		let gamma = get_gamma symb_state in
		let pat_pfs = get_pf pat_symb_state in
		let pat_gamma = get_gamma pat_symb_state in
		print_debug (Printf.sprintf "pfs: \n%s" (JSIL_Memory_Print.string_of_shallow_p_formulae pfs false));
		print_debug (Printf.sprintf "pat_pfs: \n%s" (JSIL_Memory_Print.string_of_shallow_p_formulae pat_pfs false));
		print_debug (Printf.sprintf "gamma: \n%s" (JSIL_Memory_Print.string_of_gamma gamma));
		print_debug (Printf.sprintf "%s" (JSIL_Memory_Print.string_of_substitution subst));
		let pat_pfs = pf_substitution pat_pfs subst false in
		let pat_gamma = gamma_substitution pat_gamma subst false in
		let gamma = copy_gamma gamma in
		merge_gammas gamma pat_gamma;
		let pf_list = (pfs_to_list pat_pfs) @ (pfs_to_list pfs) in
		print_debug (Printf.sprintf "About to check sat of:\n%s\ngiven\n%s" (JSIL_Memory_Print.string_of_shallow_p_formulae (DynArray.of_list pf_list) false) (JSIL_Memory_Print.string_of_gamma gamma));
		let is_sat = Pure_Entailment.check_satisfiability pf_list gamma in
		print_debug (Printf.sprintf "Satisfiable: %b" is_sat);
		is_sat in

	let transform_symb_state (spec : jsil_n_single_spec) (symb_state : symbolic_state) (quotient_heap : symbolic_heap) (quotient_preds : predicate_set) (subst : substitution) (pf_discharges : jsil_logic_assertion list) (new_gamma : typing_environment) : (symbolic_state * jsil_return_flag * jsil_logic_expr) list =

		print_debug (Printf.sprintf "Entering transform_symb_state.\n");

		let merge_symb_state_with_single_post (symb_state : symbolic_state) (post : symbolic_state) ret_var ret_flag copy_flag : (symbolic_state * jsil_return_flag * jsil_logic_expr) list =
			print_debug (Printf.sprintf "Entering merge_symb_state_with_single_post.");
			let post_makes_sense = compatible_pfs symb_state post subst in
			if (post_makes_sense) then (
				print_debug (Printf.sprintf "The post makes sense.");
				let new_symb_state = if (copy_flag) then (copy_symb_state symb_state) else symb_state in
				let new_symb_state = Structural_Entailment.merge_symb_states new_symb_state post subst in
				let ret_lexpr = store_get_var (get_store post) ret_var in
				let ret_lexpr = JSIL_Logic_Utils.lexpr_substitution ret_lexpr subst false in
				[ new_symb_state, ret_flag, ret_lexpr ])
				else begin print_debug (Printf.sprintf "The post does not make sense."); [] end in

		extend_symb_state_with_pfs symb_state (DynArray.of_list pf_discharges);
		let symb_state = symb_state_replace_heap symb_state quotient_heap in
		let symb_state = symb_state_replace_preds symb_state quotient_preds in
		let symb_state = symb_state_replace_gamma symb_state new_gamma in
		let ret_var = proc_get_ret_var proc spec.n_ret_flag in
		let ret_flag = spec.n_ret_flag in
		let symb_states_and_ret_lexprs =
			(match spec.n_post with
			| [] -> print_debug (Printf.sprintf "No postconditions found."); []
			| [ post ] -> print_debug (Printf.sprintf "One postcondition found."); merge_symb_state_with_single_post symb_state post ret_var ret_flag false
			| post :: rest_posts ->
					print_debug (Printf.sprintf "Multiple postconditions found.");
					let symb_states_and_ret_lexprs = List.map (fun post -> merge_symb_state_with_single_post symb_state post ret_var ret_flag true) rest_posts in
					let symb_states_and_ret_lexprs =
						(merge_symb_state_with_single_post symb_state post ret_var ret_flag false) :: symb_states_and_ret_lexprs in
					let symb_states_and_ret_lexprs = List.concat symb_states_and_ret_lexprs in
					symb_states_and_ret_lexprs) in
		symb_states_and_ret_lexprs in

	let enrich_pure_part symb_state spec subst : bool * symbolic_state =
		let pre_gamma = (get_gamma spec.n_pre) in
		let pre_pfs = (get_pf spec.n_pre) in
		let pre_gamma = copy_gamma pre_gamma in
		let pre_pfs = copy_p_formulae pre_pfs in
		let pfs = pf_substitution pre_pfs subst false in
		let gamma = gamma_substitution pre_gamma subst false in
		merge_gammas gamma (get_gamma symb_state);
		merge_pfs pfs (get_pf symb_state);
		let store = copy_store (get_store symb_state) in
		let heap = get_heap symb_state in
		let preds = get_preds symb_state in
		let new_symb_state = (heap, store, pfs, gamma, preds (*, ref None *)) in
		let is_sat = Pure_Entailment.check_satisfiability (get_pf_list new_symb_state) (get_gamma new_symb_state) in
		(is_sat, new_symb_state) in


	let rec find_correct_specs spec_list ac_quotients =
		match spec_list with
		| [] -> ac_quotients
		| spec :: rest_spec_list ->
			print_debug (Printf.sprintf "------------------------------------------");
			print_debug (Printf.sprintf "Entering find_correct_specs with the spec:");
			print_debug (Printf.sprintf "------------------------------------------");
			print_debug (Printf.sprintf "Pre:\n%sPosts:\n%s"
				(JSIL_Memory_Print.string_of_shallow_symb_state spec.n_pre)
				(JSIL_Memory_Print.string_of_symb_state_list spec.n_post));
			let unifier = Structural_Entailment.unify_symb_states [] spec.n_pre symb_state_aux in
			(match unifier with
			|	Some (true, quotient_heap, quotient_preds, subst, pf_discharges, new_gamma) ->
				print_debug (Printf.sprintf "I found a COMPLETE match");
				print_debug (Printf.sprintf "The pre of the spec that completely matches me is:\n%s"
					(JSIL_Memory_Print.string_of_shallow_symb_state spec.n_pre));
				print_debug (Printf.sprintf "The number of posts is: %d"
					(List.length spec.n_post));
				[ (spec, quotient_heap, quotient_preds, subst, pf_discharges, new_gamma) ]
			| Some (false, quotient_heap, quotient_preds, subst, pf_discharges, new_gamma) ->
				print_debug (Printf.sprintf "I found a PARTIAL match");
				find_correct_specs rest_spec_list ((spec, quotient_heap, quotient_preds, subst, pf_discharges, new_gamma) :: ac_quotients)

			| None -> (
				print_debug (Printf.sprintf "I found a NON-match");
				find_correct_specs rest_spec_list ac_quotients)) in


	let transform_symb_state_partial_match (spec, quotient_heap, quotient_preds, subst, pf_discharges, new_gamma) : (symbolic_state * jsil_return_flag * jsil_logic_expr) list =

		let symb_states_and_ret_lexprs = transform_symb_state spec symb_state quotient_heap quotient_preds subst pf_discharges new_gamma in

		let symb_states_and_ret_lexprs =
			List.fold_left
				(fun ac (symb_state, ret_flag, ret_lexpr) ->
					let (is_sat, new_symb_state) = enrich_pure_part symb_state spec subst in
					if is_sat then ((new_symb_state, ret_flag, ret_lexpr) :: ac) else ac)
				[] symb_states_and_ret_lexprs in

		let symb_states_and_ret_lexprs =
			List.map (fun (symb_state, ret_flag, ret_lexpr) ->
			let new_symb_state =
				let pfs = get_pf symb_state in
				let rpfs = DynArray.map (fun x -> JSIL_Logic_Utils.reduce_assertion_no_store new_gamma pfs x) pfs in
				sanitise_pfs_no_store new_gamma rpfs;
				symb_state_replace_pfs symb_state rpfs in
			(new_symb_state, ret_flag, JSIL_Logic_Utils.reduce_expression_no_store_no_gamma_no_pfs ret_lexpr)) symb_states_and_ret_lexprs in
		symb_states_and_ret_lexprs in


	let rec apply_correct_specs (quotients : (jsil_n_single_spec * symbolic_heap * predicate_set * substitution * (jsil_logic_assertion list) * typing_environment) list) =
		print_debug (Printf.sprintf "Entering apply_correct_specs.");
		match quotients with
		| [ ] -> [ ]
		| [ (spec, quotient_heap, quotient_preds, subst, pf_discharges, new_gamma) ] ->
			print_debug (Printf.sprintf "This was a TOTAL MATCH!!!!");
			transform_symb_state spec symb_state quotient_heap quotient_preds subst pf_discharges new_gamma
	 	| _ :: _ ->
			print_debug (Printf.sprintf "this was a PARTIAL MATCH!!!!");
			let new_symb_states =
				List.map
					(fun (spec, quotient_heap, quotient_preds, subst, pf_discharges, new_gamma) ->
						if (compatible_pfs symb_state spec.n_pre subst)
							then transform_symb_state_partial_match (spec, quotient_heap, quotient_preds, subst, pf_discharges, new_gamma)
							else [])
					quotients in
			let new_symb_states = List.concat new_symb_states in
			new_symb_states in

	let quotients = find_correct_specs proc_specs.n_proc_specs [] in
	apply_correct_specs quotients



let rec fold_predicate pred_name pred_defs symb_state params args existentials =

	print_time_debug ("fold_predicate:");

	(* create a new symb state with the abstract store in which the
	    called procedure is to be executed *)
	let new_store = init_store params args in
	let symb_state_aux = symb_state_replace_store symb_state new_store in

	let existentials =
		(match existentials with
		| None ->
			let symb_state_vars : (jsil_var, bool) Hashtbl.t = get_symb_state_vars_as_tbl false symb_state  in
			let args_vars : (jsil_var, bool) Hashtbl.t = JSIL_Logic_Utils.get_vars_le_list_as_tbl false args in
			let existentials : jsil_var list = JSIL_Logic_Utils.tbl_intersection_false_true symb_state_vars args_vars in
			existentials
		| Some existentials -> existentials) in

	let existentials_str = print_var_list existentials in
	print_debug (Printf.sprintf ("\nIn the FOLD with the following new variables %s: \n%s\n")
		existentials_str
		(JSIL_Memory_Print.string_of_shallow_symb_state symb_state));

	let update_symb_state_after_folding symb_state quotient_heap quotient_preds new_pfs new_gamma pred_name args =
		print_time_debug ("update_symb_state_after_folding:");
		let symb_state = symb_state_replace_heap symb_state quotient_heap in
		let symb_state = symb_state_replace_preds symb_state quotient_preds in
		let symb_state = symb_state_replace_gamma symb_state new_gamma in
		extend_symb_state_with_pfs symb_state (DynArray.of_list new_pfs);
		symb_state_add_predicate_assertion symb_state (pred_name, args);
		symb_state in

	let rec find_correct_pred_def cur_pred_defs =
		print_time_debug ("find_correct_pred_def:");
		(match cur_pred_defs with
		| [] -> None
		| pred_def :: rest_pred_defs ->
			print_debug (Printf.sprintf "----------------------------");
			print_debug (Printf.sprintf "Current pred symbolic state: %s" (JSIL_Memory_Print.string_of_shallow_symb_state pred_def));
			let unifier = Structural_Entailment.unify_symb_states_fold existentials pred_def symb_state_aux in
			(match unifier with
			| Some (true, quotient_heap, quotient_preds, subst, pf_discharges, new_gamma, _, []) ->
			  print_debug (Printf.sprintf "I can fold this!!!");
				let new_symb_state = update_symb_state_after_folding symb_state quotient_heap quotient_preds pf_discharges new_gamma pred_name args in
				print_debug (Printf.sprintf "Symbolic state after FOLDING:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state new_symb_state));
				Some new_symb_state

			| Some (true, quotient_heap, quotient_preds, subst, pf_discharges, new_gamma, existentials, [ (missing_pred_name, missing_pred_args) ]) ->
				let missing_pred_args = List.map (fun le -> JSIL_Logic_Utils.lexpr_substitution le subst false) missing_pred_args in
				if (not (missing_pred_name = pred_name)) then None else (
					print_debug (Printf.sprintf "I can NOT quite fold this because I am missing %s(%s)!!!"
						missing_pred_name
						(String.concat ", " (List.map (fun le -> JSIL_Print.string_of_logic_expression le false) missing_pred_args)));
					let new_symb_state = update_symb_state_after_folding symb_state quotient_heap quotient_preds pf_discharges new_gamma pred_name args in
					print_debug (Printf.sprintf "Symbolic state after partial FOLDING:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state new_symb_state));
					let new_symb_state = fold_predicate pred_name pred_defs new_symb_state params missing_pred_args (Some existentials) in
					(match new_symb_state with
					| Some new_symb_state ->
						remove_predicate_assertion (get_preds new_symb_state) (missing_pred_name, missing_pred_args);
						Some new_symb_state
					| None -> None))

			| Some (_, _, _, _, _, _, _, _) | None -> find_correct_pred_def rest_pred_defs)) in
	find_correct_pred_def pred_defs


(* SYMBOLIC STATE SIMPLIFICATION *)

let rec get_list_nth_len_ass subst in_not a =
	let f = get_list_nth_len_ass subst in
	(match a with
	| LAnd  (a1, a2)
	| LOr   (a1, a2)
	| LStar	(a1, a2) -> f in_not a1; f in_not a2
	| LNot a -> f (not in_not) a
	| LTrue
	| LFalse
	| LEmp
	| LLess	   	(_, _)
	| LLessEq	(_, _)
	| LStrLess  (_, _)
	| LPointsTo	(_, _, _)
	| LPred (_, _)
	| LTypes _ -> ()
	| LEq (e1, e2) -> if in_not then () else
		(match e1, e2 with
		| LVar var, LLit (LList l1)
		| LLit (LList l1), LVar var -> Hashtbl.replace subst var (LLit (LList l1))
		| LVar var, LEList l1
		| LEList l1, LVar var -> Hashtbl.replace subst var (LEList l1)
		| _, _ -> ()))

let rec subst_list_nth_len_e subst e =
	let f = subst_list_nth_len_e subst in
	(match e with
	| LBinOp (e1, op, e2) -> LBinOp (f e1, op, f e2)
	| LUnOp	(op, e) -> LUnOp (op, e)
	| LTypeOf e -> LTypeOf (f e)
	| LEList le -> LEList (List.map (fun x -> f x) le)
	| LStrNth (str, index) -> LStrNth (f str, f index)
	(* THIS IS THE POINT *)
	| LLstNth (lst, index) ->
		let idx = (match index with
					| LLit (Integer i) -> Some i
					| LLit (Num n) -> Some (int_of_float n)
					| _ -> None) in
		(match lst with
		  | LVar var ->
		  	if (Hashtbl.mem subst var) then
			begin
				let lst = Hashtbl.find subst var in
				(match idx with
				| Some i ->
					(match lst with
					| LLit (LList l) -> LLit (List.nth l i)
					| LEList l -> List.nth l i
					| _ -> e)
				| None -> e)
			end
			else e
		  | LEList lst ->
			  (match idx with
				| Some i -> List.nth lst i
				| None -> e)
		  | LLit (LList lst) ->
			  (match idx with
				| Some i -> LLit (List.nth lst i)
				| None -> e)
		  | _ -> e)
    | _ -> e)

let rec subst_list_nth_len_pf subst a =
	let f = subst_list_nth_len_pf subst in
	let fe = subst_list_nth_len_e subst in
	(match a with
	| LAnd  (a1, a2) -> LAnd (f a1, f a2)
	| LOr   (a1, a2) -> LOr (f a1, f a2)
	| LStar	(a1, a2) -> LStar (f a1, f a2)
	| LNot a -> LNot (f a)
	| LEq       (e1, e2) -> LEq (fe e1, fe e2)
	| LLess	   	(e1, e2) -> LLess (fe e1, fe e2)
	| LLessEq	(e1, e2) -> LLessEq (fe e1, fe e2)
	| LStrLess  (e1, e2) -> LStrLess (fe e1, fe e2)
	| LPointsTo	(e1, e2, e3) -> LPointsTo (fe e1, fe e2, fe e3)
	| _ -> a)

let expand_gamma gamma pure_formulae =
	DynArray.iter
		(fun a -> match a with
			| LEq (LVar a, LVar b) ->
				let if_mem var = if (Hashtbl.mem gamma var) then (Some (Hashtbl.find gamma var)) else None in
				let ta = if_mem a in let tb = if_mem b in
				(match ta, tb with
			     | Some ta, None -> update_gamma gamma b (Some ta)
				 | None, Some tb -> update_gamma gamma a (Some tb)
				 | _, _ -> ())
			| _ -> ())
		pure_formulae;
	gamma

let simplify_symb_state symb_state =
	let heap, store, pure_formulae, gamma, preds (*, solver *) = symb_state in
	let list_subst = Hashtbl.create 17 in
	DynArray.iter (fun a -> get_list_nth_len_ass list_subst false a) pure_formulae;
	sanitise_pfs store gamma pure_formulae;
	let new_gamma = expand_gamma gamma pure_formulae in
	(heap, store, pure_formulae, new_gamma, preds (*, solver *))



let unfold_predicates pred_name pred_defs symb_state params args spec_vars =
	print_debug (Printf.sprintf "Current symbolic state:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state));

	let subst0 = Symbolic_State_Functions.subtract_pred pred_name args (get_preds symb_state) (get_pf symb_state) (* (get_solver symb_state) *) (get_gamma symb_state) spec_vars in
	let args = List.map (fun le -> lexpr_substitution le subst0 true) args in
	let calling_store = init_store params args in

	let rec loop pred_defs (symb_states : symbolic_state list) =
		(match pred_defs with
		| [] -> symb_states
		| pred_symb_state :: rest_pred_defs ->
			print_debug (Printf.sprintf "Current Pred DEF:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state pred_symb_state));
			print_debug (Printf.sprintf "Current symbolic state:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state));
			let unfolded_symb_state = Structural_Entailment.unfold_predicate_definition symb_state pred_symb_state calling_store subst0 spec_vars in
			(match unfolded_symb_state with
			| None -> loop rest_pred_defs symb_states
			| Some unfolded_symb_state ->
				loop rest_pred_defs (unfolded_symb_state :: symb_states))) in

	loop pred_defs []


let recursive_unfold pred_name pred_defs symb_state params spec_vars =

	let rec loop symb_state =
		let rec aux symb_state args =
			print_debug (Printf.sprintf "pred_args: %s\n"
				(String.concat ", " (List.map (fun le -> JSIL_Print.string_of_logic_expression le false) args)));
			let unfolded_symb_states = unfold_predicates pred_name pred_defs symb_state params args spec_vars in
			print_debug (Printf.sprintf "number of unfolded_symb_states: %i\n" (List.length unfolded_symb_states));
			if ((List.length unfolded_symb_states > 1) || (List.length unfolded_symb_states = 0))
				then (print_debug (Printf.sprintf "More than one unfolding or nothing at all, oops.\n"); symb_state)
				else (
					let new_symb_state = simplify false (List.hd unfolded_symb_states) in
					print_debug (Printf.sprintf "Inside recursive unfolding:\n%s\n" (JSIL_Memory_Print.string_of_shallow_symb_state new_symb_state));
					loop new_symb_state) in

		let rec inner_loop pred_args symb_state =
			match pred_args with
			| [] -> symb_state
			| args :: more_args ->
				aux symb_state args in

		let pred_args = find_predicate_assertion (get_preds symb_state) pred_name in
		let len_pred_args = List.length pred_args in
		print_debug (Printf.sprintf "len_pred_args: %i\n" len_pred_args);
		inner_loop pred_args symb_state in

	loop symb_state





let rec symb_evaluate_logic_cmd s_prog l_cmd symb_state subst spec_vars =

	let get_pred_data pred_name les =
		let pred = get_pred s_prog.pred_defs pred_name in
		let args =
			List.map
				(fun le -> JSIL_Logic_Normalise.normalise_lexpr (get_store symb_state) (get_gamma symb_state) subst le)
				les in
		let params = pred.n_pred_params in
		let pred_defs = pred.n_pred_definitions in
		(params, pred_defs, args) in

	(match l_cmd with
	| Fold a ->
		print_time "Fold.";
		(match a with
		| LPred	(pred_name, les) ->
			let params, pred_defs, args = get_pred_data pred_name les in
			let new_symb_state = fold_predicate pred_name pred_defs symb_state params args None in
			(match new_symb_state with
			| Some symb_state ->
				[ symb_state ]
			| None ->
				print_endline (Printf.sprintf "\nSTATE ON ERROR: %s" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state));
				let msg = Printf.sprintf "Could not fold: %s " (JSIL_Print.string_of_logic_assertion a false) in
				raise (Failure msg))
		| _ ->
			let msg = Printf.sprintf "Illegal fold command %s" (JSIL_Print.string_of_logic_assertion a false) in
			raise (Failure msg))

	| Unfold a ->
		print_time "Unfold.";
		(match a with
		| LPred (pred_name, les) ->
			let params, pred_defs, args = get_pred_data pred_name les in
			let symb_states = unfold_predicates pred_name pred_defs symb_state params args spec_vars in
			if ((List.length symb_states) = 0) then (
				print_endline (Printf.sprintf "\nCould not unfold: %s" pred_name);
				let msg = Printf.sprintf "Could not unfold: %s " (JSIL_Print.string_of_logic_assertion a false) in
				raise (Failure msg))
			else symb_states
		| _ ->
			let msg = Printf.sprintf "Illegal unfold command %s" (JSIL_Print.string_of_logic_assertion a false) in
			raise (Failure msg))

	| RecUnfold pred_name ->
		print_time "RecUnfold.";
		let pred = get_pred s_prog.pred_defs pred_name in
		let pred_defs = pred.n_pred_definitions in
		let params = pred.n_pred_params in
		[ recursive_unfold pred_name pred_defs symb_state params spec_vars ]

	| LogicIf (le, then_lcmds, else_lcmds) ->
		print_time "LIf.";
		let le' = JSIL_Logic_Normalise.normalise_lexpr (get_store symb_state) (get_gamma symb_state) (init_substitution []) le in
		let e_le', a_le' = lift_logic_expr le' in
		let a_le_then =
			match e_le', a_le' with
			| _, Some a_le -> a_le
			| Some e_le, None -> LEq (e_le, LLit (Bool true))
			| None, None -> LFalse in
		if (Pure_Entailment.old_check_entailment [] (get_pf_list symb_state) [ a_le_then ] (get_gamma symb_state))
			then symb_evaluate_logic_cmds s_prog then_lcmds [ symb_state ] subst spec_vars
			else symb_evaluate_logic_cmds s_prog else_lcmds [ symb_state ] subst spec_vars )
and
symb_evaluate_logic_cmds s_prog (l_cmds : jsil_logic_command list) (symb_states : symbolic_state list) subst spec_vars =
	let symb_states = List.map (fun s -> simplify false s) symb_states in
	match l_cmds with
	| [] -> symb_states
	| l_cmd :: rest_l_cmds ->
		let new_symb_states =
			List.fold_left
				(fun ac_new_symb_states symb_state ->
					let new_symb_states = symb_evaluate_logic_cmd s_prog l_cmd symb_state subst spec_vars in
					new_symb_states @ ac_new_symb_states)
				[]
				symb_states in
		symb_evaluate_logic_cmds s_prog rest_l_cmds new_symb_states subst spec_vars


let rec symb_evaluate_cmd s_prog proc spec search_info symb_state i prev =

	(* auxiliary functions *)
	let mark_as_visited search_info i =
		let cur_node_info = search_info.cur_node_info in
		Hashtbl.replace search_info.vis_tbl i cur_node_info.node_number in


	let print_symb_state_and_cmd symb_state =
		let symb_state_str = JSIL_Memory_Print.string_of_shallow_symb_state symb_state in
		let cmd = get_proc_cmd proc i in
		let cmd_str = JSIL_Print.string_of_cmd cmd 0 0 false false false in
		let time = Sys.time() in
		print_endline (Printf.sprintf
			"----------------------------------\n--%i--\nTIME: %f\nSTATE:\n%sCMD: %s\n----------------------------------"
			i time symb_state_str cmd_str) in


	(* symbolically evaluate a guarded goto *)
	let symb_evaluate_guarded_goto symb_state e j k =
		let le = symb_evaluate_expr e (get_store symb_state) (get_gamma symb_state) (get_pf symb_state) in
		print_debug (Printf.sprintf "Evaluated expression: %s --> %s\n" (JSIL_Print.string_of_expression e false) (JSIL_Print.string_of_logic_expression le false));
		let e_le, a_le = lift_logic_expr le in
		let a_le_then, a_le_else =
			match e_le, a_le with
			| _, Some a_le ->
				print_debug (Printf.sprintf "Lifted assertion: %s\n" (JSIL_Print.string_of_logic_assertion a_le false));
				([ a_le ], [ (LNot a_le) ])
			| Some e_le, None ->
				([LEq (e_le, LLit (Bool true))], [LEq (e_le, LLit (Bool false))])
			| None, None -> ([ LFalse ], [ LFalse ]) in

		print_debug (Printf.sprintf "Checking if:\n%s\n\tentails\n%s\n" (JSIL_Print.str_of_assertion_list (get_pf_list symb_state)) (JSIL_Print.str_of_assertion_list a_le_then));
		if (Pure_Entailment.old_check_entailment [] (get_pf_list symb_state) a_le_then (get_gamma symb_state)) then
			(print_endline "in the THEN branch";
			symb_evaluate_next_cmd_1 s_prog proc spec search_info symb_state i j)
			else (if (Pure_Entailment.old_check_entailment [] (get_pf_list symb_state) a_le_else (get_gamma symb_state)) then
					(print_endline "in the ELSE branch";
					symb_evaluate_next_cmd_1 s_prog proc spec search_info symb_state i k)
				else
					(print_endline "I could not determine the branch.";

					let then_symb_state = symb_state in
					let then_search_info = search_info in
					let else_symb_state = copy_symb_state symb_state in
					let else_search_info = update_vis_tbl search_info (copy_vis_tbl search_info.vis_tbl) in

					extend_symb_state_with_pfs then_symb_state (DynArray.of_list a_le_then);
					symb_evaluate_next_cmd_1 s_prog proc spec then_search_info then_symb_state i j;
					extend_symb_state_with_pfs else_symb_state (DynArray.of_list a_le_else);
					symb_evaluate_next_cmd_1 s_prog proc spec else_search_info else_symb_state i k)) in


	(* symbolically evaluate a procedure call *)
	let symb_evaluate_call symb_state x e e_args j =

		(* get the name and specs of the procedure being called *)
		let le_proc_name = symb_evaluate_expr e (get_store symb_state) (get_gamma symb_state) (get_pf symb_state) in
		let proc_name =
			(match le_proc_name with
			| LLit (String proc_name) -> proc_name
			| _ ->
				let msg = Printf.sprintf "Symb Execution Error - Cannot analyse a procedure call without the name of the procedure. Got: %s." (JSIL_Print.string_of_logic_expression le_proc_name false) in
				raise (Failure msg)) in
		let proc_specs =
			(try
				Hashtbl.find s_prog.spec_tbl proc_name
			with _ ->
				let msg = Printf.sprintf "No spec found for proc %s" proc_name in
				raise (Failure msg)) in

		List.iter (fun spec -> if (spec.n_post = []) then print_debug "Exists spec with no post.") proc_specs.n_proc_specs;

		(* symbolically evaluate the args *)
		let le_args = List.map (fun e -> symb_evaluate_expr e (get_store symb_state) (get_gamma symb_state) (get_pf symb_state)) e_args in
		let new_symb_states = find_and_apply_spec s_prog.program proc_name proc_specs symb_state le_args in

		(if ((List.length new_symb_states) = 0)
			then raise (Failure (Printf.sprintf "No precondition found for procedure %s." proc_name)));

		List.iter
			(fun (symb_state, ret_flag, ret_le) ->
				let ret_type, _, _ =	type_lexpr (get_gamma symb_state) ret_le in
				update_abs_store (get_store symb_state) x ret_le;
				update_gamma (get_gamma symb_state) x ret_type;
				let new_search_info = update_vis_tbl search_info (copy_vis_tbl search_info.vis_tbl) in
				(match ret_flag, j with
				| Normal, _ ->
					symb_evaluate_next_cmd_1 s_prog proc spec new_search_info symb_state i (i+1)
				| Error, None -> raise (Failure (Printf.sprintf "Procedure %s may return an error, but no error label was provided." proc_name))
				| Error, Some j ->
					symb_evaluate_next_cmd_1 s_prog proc spec new_search_info symb_state i j))
			new_symb_states in

	(* symbolically evaluate a phi command *)
	let symb_evaluate_phi symb_state x x_arr =
		let cur_proc_name = proc.proc_name in
		let cur_which_pred =
			try Hashtbl.find s_prog.which_pred (cur_proc_name, prev, i)
			with _ ->  raise (Failure (Printf.sprintf "which_pred undefined for command: %s %d %d" cur_proc_name prev i)) in
		let expr = x_arr.(cur_which_pred) in
		let le = symb_evaluate_expr expr (get_store symb_state) (get_gamma symb_state) (get_pf symb_state) in
		let te, _, _ =	type_lexpr (get_gamma symb_state) le in
		update_abs_store (get_store symb_state) x le;
		update_gamma (get_gamma symb_state) x te;
		symb_evaluate_next_cmd_1 s_prog proc spec search_info symb_state i (i+1) in

	let symb_state = simplify false symb_state in
	print_symb_state_and_cmd symb_state;
	let metadata, cmd = get_proc_cmd proc i in
	mark_as_visited search_info i;
	match cmd with
	| SBasic bcmd ->
		let _ = symb_evaluate_bcmd bcmd symb_state in
		symb_evaluate_next_cmd_1 s_prog proc spec search_info symb_state i (i+1)

	| SGoto j -> symb_evaluate_next_cmd_1 s_prog proc spec search_info symb_state i j

	| SGuardedGoto (e, j, k) -> symb_evaluate_guarded_goto symb_state e j k

	| SCall (x, e, e_args, j) -> symb_evaluate_call symb_state x e e_args j

	| SPhiAssignment (x, x_arr) -> symb_evaluate_phi symb_state x x_arr

	| _ -> raise (Failure "not implemented yet")

and symb_evaluate_next_cmd_1 s_prog proc spec search_info symb_state cur next  =
	let metadata, cmd = get_proc_cmd proc cur in
	let symb_states = symb_evaluate_logic_cmds s_prog metadata.post_logic_cmds [ symb_state ] spec.n_subst spec.n_lvars in
	let len = List.length symb_states in
	List.iter
		(fun symb_state ->
			let search_info =
				if (len > 1)
					then {	search_info with vis_tbl = (copy_vis_tbl search_info.vis_tbl) }
					else search_info in
				symb_evaluate_next_cmd_2 s_prog proc spec search_info symb_state cur next)
		symb_states

and symb_evaluate_next_cmd_2 s_prog proc spec search_info symb_state cur next  =

	(* auxiliary function *)
	let is_visited i =
		(try
			let _ = Hashtbl.find search_info.vis_tbl i in
			true
		with _ -> false) in

	(* test if the control reached the end of the symbolic execution *)
	if ((Some cur) = proc.ret_label) then
		(Structural_Entailment.unify_symb_state_against_post proc.proc_name spec symb_state Normal search_info;
		Symbolic_Traces.create_info_node_from_post search_info spec.n_post Normal true; ())
	else (if ((Some cur) = proc.error_label) then
		(Structural_Entailment.unify_symb_state_against_post proc.proc_name spec symb_state Error search_info;
		Symbolic_Traces.create_info_node_from_post search_info spec.n_post Error true; ())
	else
		(* the control did not reach the end of the symbolic execution *)
		begin
			let metadata, cmd = get_proc_cmd proc next in
			if (is_visited next) then
				(* a loop was found *)
				begin
					match (metadata.pre_cond) with
					| None -> raise (Failure "back edges need to point to commands annotated with invariants")
					| Some a ->
						(* check if the current symbolic state entails the invariant *)
						let new_symb_state, _ = JSIL_Logic_Normalise.normalise_postcondition a spec.n_subst spec.n_lvars (get_gamma spec.n_pre) in
						(match (Structural_Entailment.fully_unify_symb_state new_symb_state symb_state spec.n_lvars) with
						| Some _, _ -> ()
						| None, msg -> raise (Failure msg))
				end
			else
				(* no loop found *)
				begin
					let symb_state =
						match (metadata.pre_cond) with
						| None -> symb_state
						| Some a ->
							let new_symb_state, _ = JSIL_Logic_Normalise.normalise_postcondition a spec.n_subst spec.n_lvars (get_gamma spec.n_pre) in
							(match (Structural_Entailment.fully_unify_symb_state new_symb_state symb_state spec.n_lvars) with
							| Some _, _ -> new_symb_state
							| None, msg -> raise (Failure msg)) in


					let symb_states = symb_evaluate_logic_cmds s_prog metadata.pre_logic_cmds [ symb_state ] spec.n_subst spec.n_lvars in
					let len = List.length symb_states in
					List.iter
						(fun symb_state ->
							let vis_tbl = if (len > 1) then (copy_vis_tbl search_info.vis_tbl) else search_info.vis_tbl in
							let info_node = Symbolic_Traces.create_info_node_from_cmd search_info symb_state cmd next in
							let new_search_info = udpdate_search_info search_info info_node vis_tbl in
							symb_evaluate_cmd s_prog proc spec new_search_info symb_state next cur)
						symb_states
				end
		end)


let symb_evaluate_proc s_prog proc_name spec i pruning_info =
	let node_info = Symbolic_Traces.create_info_node_aux spec.n_pre 0 (-1) "Precondition" in
	let search_info = make_symb_exe_search_info node_info pruning_info i in

	let proc = get_proc s_prog.program proc_name in
	let sep_str = "----------------------------------\n" in

	print_endline (Printf.sprintf "%s" (sep_str ^ sep_str ^ "Symbolic execution of " ^ proc_name));
	let success, failure_msg =
		(try
			print_debug (Printf.sprintf "Initial symbolic state:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state spec.n_pre));
			let symb_state = copy_symb_state spec.n_pre in
			let symb_state = simplify_symb_state (symb_state) in
			symb_evaluate_next_cmd_2 s_prog proc spec search_info symb_state (-1) 0;
			true, None
		with Failure msg ->
			(print_endline (Printf.sprintf "The EVALUATION OF THIS PROC GAVE AN ERROR: %d %s!!!!" i msg);
			Symbolic_Traces.create_info_node_from_error search_info msg;
			Symbolic_Traces.create_info_node_from_post search_info spec.n_post spec.n_ret_flag false;
			false, Some msg)) in
	let proc_name = Printf.sprintf "Spec_%d_of_%s" i proc_name in
	let search_dot_graph = Some (JSIL_Memory_Print.dot_of_search_info search_info proc_name) in
	print_debug (Printf.sprintf "%s" (sep_str ^ sep_str ^ sep_str));
	search_dot_graph, success, failure_msg



let sym_run_procs procs_to_verify spec_table prog which_pred pred_defs =
	let n_pred_defs = JSIL_Logic_Normalise.normalise_predicate_definitions pred_defs in
	let s_prog = {
		program = prog;
		which_pred = which_pred;
		spec_tbl = spec_table;
		pred_defs = n_pred_defs
	} in
	let pruning_info = init_post_pruning_info () in
	let results = Hashtbl.fold
		(fun proc_name spec ac_results ->
			let should_we_verify = (Hashtbl.mem procs_to_verify proc_name) in
			if (should_we_verify) then
			begin
				update_post_pruning_info_with_spec pruning_info spec;
				let pre_post_list = spec.n_proc_specs in
				let results =
					List.mapi
					(fun i pre_post ->
						let new_pre_post = Symbolic_State_Functions.copy_single_spec pre_post in
						let dot_graph, success, failure_msg =
							if (should_we_verify)
								then symb_evaluate_proc s_prog proc_name new_pre_post i pruning_info
								else
								begin
									let post_pruning_info_array_list = Hashtbl.find pruning_info proc_name in
									let post_pruning_info_array = List.nth post_pruning_info_array_list i in
									Array.fill post_pruning_info_array 0 (Array.length post_pruning_info_array) true;
									None, true, None
								end in
						(proc_name, i, pre_post, success, failure_msg, dot_graph))
					pre_post_list in
				let new_spec = { spec with n_proc_specs = (filter_useless_posts_in_multiple_specs proc_name pre_post_list pruning_info) } in
				Hashtbl.replace spec_table proc_name new_spec;
				ac_results @ results
			end
			else ac_results)
		spec_table
		[] in
	let complete_success =
		List.fold_left
			(fun ac (_, _, _, partial_success, _, _) ->
				if (ac && partial_success) then true else false)
			true
			results in
	let results_str, dot_graphs = JSIL_Memory_Print.string_of_symb_exe_results results in
	let count_prunings = ref 0 in
	let count_verified = ref 0 in
	Hashtbl.iter
		(fun proc_name spec ->
			let should_we_verify = (Hashtbl.mem procs_to_verify proc_name) in
			if (should_we_verify) then
				let pruning_info_list = Hashtbl.find pruning_info proc_name in
				List.iter (fun l ->
					Array.iter (fun l -> if l then count_verified := !count_verified + 1
						                      else count_prunings := !count_prunings + 1) l) pruning_info_list
			)
		spec_table;
	print_endline (Printf.sprintf "\nVerified: %d.\t\tPrunings: %d.\n" !count_verified !count_prunings);
	results_str, dot_graphs, complete_success
