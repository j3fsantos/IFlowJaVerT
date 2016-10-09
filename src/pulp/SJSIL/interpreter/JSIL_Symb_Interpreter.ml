open JSIL_Syntax
open JSIL_Memory_Model
open JSIL_Logic_Utils

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
			let l = JSIL_Interpreter.evaluate_binop op l1 l2 in
			LLit l
		| _, _ -> LBinOp (nle1, op, nle2))

	| UnaryOp (op, e) ->
		let nle = symb_evaluate_expr e store gamma pure_formulae in
		(match nle with
		| LLit lit -> LLit (JSIL_Interpreter.evaluate_unop op lit)
		| _ -> LUnOp (op, nle))

	| TypeOf (e) ->
		(** the typeof can only be removed when there are no constraints
        If there are constraints, we need to leave it there because
				the constraints cannot be ignored.                       **)
		let nle = symb_evaluate_expr e store gamma pure_formulae in
		let nle_type, _, _ = type_lexpr gamma nle in
		(match nle_type with
		| Some nle_type -> LLit (Type nle_type)
		| None          ->  LTypeOf (nle))

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
		(match list, index with
		| LLit (LList list), LLit (Num n) ->
			(try (LLit (List.nth list (int_of_float n))) with _ ->
					raise (Failure "List index out of bounds"))

		| LEList list, LLit (Num n) ->
			(try (List.nth list (int_of_float n)) with _ ->
					raise (Failure "List index out of bounds"))

		| _, _ -> LLstNth (list, index))

	| StrNth (e1, e2) ->
		let str = symb_evaluate_expr e1 store gamma pure_formulae in
		let index = symb_evaluate_expr e2 store gamma  pure_formulae in
		(match str, index with
		| LLit (String s), LLit (Num n) ->
			LLit (String (String.make 1 (String.get s (int_of_float n))))
		| _, _ -> LStrNth (str, index))

	| _ -> raise (Failure "not supported yet")


let safe_symb_evaluate_expr (expr : jsil_expr) store gamma pure_formulae  =
	let nle = symb_evaluate_expr expr store gamma pure_formulae in
	(* Printf.printf "safe_symb_evaluate_expr with expr: %s!\n" (JSIL_Print.string_of_logic_expression nle false);  *)
	let nle_type, is_typable, constraints = type_lexpr gamma nle in
	(* Printf.printf "is_typable: %b\nconstraints: %s\n" is_typable (JSIL_Print.str_of_assertion_list constraints); *)
	let are_constraints_satisfied =
		(if ((List.length constraints) > 0)
			then Pure_Entailment.check_entailment [] (pfs_to_list pure_formulae) constraints gamma
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


let symb_evaluate_bcmd bcmd symb_state =
	let heap, store, pure_formulae, gamma, _ = symb_state in
	match bcmd with
	| SSkip ->
		LLit Empty

	| SAssignment (x, e) ->
		let nle, t_le, _ = safe_symb_evaluate_expr e store gamma pure_formulae in
		update_abs_store store x nle;
		update_gamma gamma x t_le;
		nle

	| SNew x ->
		let new_loc = fresh_aloc () in
		Symbolic_State_Functions.update_abs_heap_default heap new_loc LNone;
		Symbolic_State_Functions.update_abs_heap heap new_loc (LLit (String proto_f)) (LLit Null) pure_formulae gamma;
		update_abs_store store x (ALoc new_loc);
		update_gamma gamma x (Some ObjectType);
		ALoc new_loc

	| SLookup (x, e1, e2) ->
		let ne1, t_le1, _ = safe_symb_evaluate_expr e1 store gamma pure_formulae in
		let ne2, t_le2, _ = safe_symb_evaluate_expr e2 store gamma pure_formulae in
		let l =
			(match ne1 with
			| LLit (Loc l)
			| ALoc l -> l
			| _ ->
			let ne1_str = JSIL_Print.string_of_logic_expression ne1 false  in
			let msg = Printf.sprintf "I do not know which location %s denotes in the symbolic heap" ne1_str in
			raise (Failure msg)) in
		let ne = Symbolic_State_Functions.abs_heap_find heap l ne2 pure_formulae gamma in
		update_abs_store store x ne;
		ne

	| SMutation (e1, e2, e3) ->
		let ne1, t_le1, _ = safe_symb_evaluate_expr e1 store gamma pure_formulae in
		let ne2, t_le2, _ = safe_symb_evaluate_expr e2 store gamma pure_formulae in
		let ne3, _, _ = safe_symb_evaluate_expr e3 store gamma pure_formulae in
		(match ne1 with
		| LLit (Loc l)
		| ALoc l ->
			(* Printf.printf "I am going to call: Update Abstract Heap\n"; *)
			Symbolic_State_Functions.update_abs_heap heap l ne2 ne3 pure_formulae gamma
		| _ ->
			let ne1_str = JSIL_Print.string_of_logic_expression ne1 false  in
			let msg = Printf.sprintf "I do not know which location %s denotes in the symbolic heap" ne1_str in
			raise (Failure msg));
		ne3

	| SDelete (e1, e2) ->
		let ne1, t_le1, _ = safe_symb_evaluate_expr e1 store gamma pure_formulae in
		let ne2, t_le2, _ = safe_symb_evaluate_expr e2 store gamma pure_formulae in
		let l =
			(match ne1 with
			| LLit (Loc l)
			| ALoc l -> l
			| _ ->
				let ne1_str = JSIL_Print.string_of_logic_expression ne1 false  in
				let msg = Printf.sprintf "I do not know which location %s denotes in the symbolic heap" ne1_str in
				raise (Failure msg)) in
		Symbolic_State_Functions.update_abs_heap heap l ne2 LNone pure_formulae gamma;
		LLit (Bool true)

	| SHasField (x, e1, e2) ->
		let ne1, t_le1, _ = safe_symb_evaluate_expr e1 store gamma pure_formulae in
		let ne2, t_le2, _ = safe_symb_evaluate_expr e2 store gamma pure_formulae in
		match ne1 with
		| LLit (Loc l)
		| ALoc l ->
			let res = Symbolic_State_Functions.abs_heap_check_field_existence heap l ne2 pure_formulae gamma in
			update_gamma gamma x (Some BooleanType);
			(match res with
			| Some res ->
				let res_lit = LLit (Bool res) in
				update_abs_store store x res_lit;
				res_lit
			| None -> LUnknown)
		| _ ->
			let ne1_str = JSIL_Print.string_of_logic_expression ne1 false  in
			let msg = Printf.sprintf "I do not know which location %s denotes in the symbolic heap" ne1_str in
			raise (Failure msg);

	| _ ->
		raise (Failure "not implemented yet!")



let find_and_apply_spec prog proc_name proc_specs symb_state le_args =

	(* create a new symb state with the abstract store in which the
	    called procedure is to be executed *)
	let proc = get_proc prog proc_name in
	let proc_args = get_proc_args proc in
	let new_store = JSIL_Logic_Normalise.init_store proc_args le_args in
	let symb_state_aux = symb_state_replace_store symb_state new_store in

	let transform_symb_state spec symb_state quotient_heap quotient_preds subst pf_discharges =
		(* Printf.printf "I found the the spec that needs to be applied.\nThe spec pre is:\n%sThe spec post is:\n%sThe substitution is: %s"
				(JSIL_Memory_Print.string_of_shallow_symb_state spec.n_pre)
				(JSIL_Memory_Print.string_of_symb_state_list spec.n_post)
				(JSIL_Memory_Print.string_of_substitution subst); *)

		(* Printf.printf "the quotient heap is the following: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_heap quotient_heap false); *)

		let merge_symb_state_with_single_post symb_state post ret_var ret_flag copy_flag =
			let new_symb_state = if (copy_flag) then (copy_symb_state symb_state) else symb_state in
			let new_symb_state = Symbolic_State_Functions.merge_symb_states new_symb_state post subst in
			let ret_lexpr = store_get_var (get_store post) ret_var in
			let ret_lexpr = JSIL_Logic_Utils.lexpr_substitution ret_lexpr subst false in
			new_symb_state, ret_flag, ret_lexpr in

		extend_symb_state_with_pfs symb_state pf_discharges;
		let symb_state = Symbolic_State_Functions.symb_state_replace_heap symb_state quotient_heap in
		let symb_state = Symbolic_State_Functions.symb_state_replace_preds symb_state quotient_preds in
		let ret_var = proc_get_ret_var proc spec.n_ret_flag in
		let ret_flag = spec.n_ret_flag in
		let symb_states_and_ret_lexprs =
			(match spec.n_post with
			| [] -> []
			| [ post ] -> [ merge_symb_state_with_single_post symb_state post ret_var ret_flag false ]
			| post :: rest_posts ->
					let symb_states_and_ret_lexprs =
						List.map (fun post -> merge_symb_state_with_single_post symb_state post ret_var ret_flag true) rest_posts in
					let symb_states_and_ret_lexprs =
						(merge_symb_state_with_single_post symb_state post ret_var ret_flag false) :: symb_states_and_ret_lexprs in
					symb_states_and_ret_lexprs) in
		symb_states_and_ret_lexprs in

	let enrich_pure_part symb_state spec subst =
		let pre_gamma = (get_gamma spec.n_pre) in
		let pre_pfs = (get_pf spec.n_pre) in
		let pre_gamma = copy_gamma pre_gamma in
		let pre_pfs = copy_p_formulae pre_pfs in
		let pfs = Symbolic_State_Functions.pf_substitution pre_pfs subst false in
		let gamma = Symbolic_State_Functions.gamma_substitution pre_gamma subst false in
		Symbolic_State_Functions.merge_gammas gamma (get_gamma symb_state);
		Symbolic_State_Functions.merge_pfs pfs (get_pf symb_state);
		let store = copy_store (get_store symb_state) in
		let heap = get_heap symb_state in
		let preds = get_preds symb_state in
		let new_symb_state = (heap, store, pfs, gamma, preds) in
		new_symb_state in


	let rec find_correct_specs spec_list ac_quotients =
		match spec_list with
		| [] -> ac_quotients
		| spec :: rest_spec_list ->
			(* Printf.printf "------------------------------------------\n";
			Printf.printf "Entering find_correct_specs with the sepc:\n";
			Printf.printf "------------------------------------------\n";
			Printf.printf "Pre:\n%sPosts:\n%s"
				(JSIL_Memory_Print.string_of_shallow_symb_state spec.n_pre)
				(JSIL_Memory_Print.string_of_symb_state_list spec.n_post); *)
			let unifier = Structural_Entailment.unify_symb_states [] spec.n_pre symb_state_aux in
			(match unifier with
			|	Some (quotient_heap, quotient_preds, subst, pf_discharges, true) ->
				(* Printf.printf "I found a COMPLETE match\n"; *)
				[ (spec, quotient_heap, quotient_preds, subst, pf_discharges) ]
			| Some (quotient_heap, quotient_preds, subst, pf_discharges, false) ->
				(* Printf.printf "I found a PARTIAL match\n"; *)
				find_correct_specs rest_spec_list ((spec, quotient_heap, quotient_preds, subst, pf_discharges) :: ac_quotients)
			| None -> (
				(* Printf.printf "I found a NON-match\n"; *)
				find_correct_specs rest_spec_list ac_quotients)) in


	let transform_symb_state_partial_match (spec, quotient_heap, quotient_preds, subst, pf_discharges) =
		let symb_states_and_ret_lexprs = transform_symb_state spec symb_state quotient_heap quotient_preds subst pf_discharges in
		let symb_states_and_ret_lexprs =
			List.map
				(fun (symb_state, ret_flag, ret_lexpr) ->
					let new_symb_state = enrich_pure_part symb_state spec subst in
					(new_symb_state, ret_flag, ret_lexpr))
			symb_states_and_ret_lexprs in
		symb_states_and_ret_lexprs in


	let rec apply_correct_specs quotients =
		match quotients with
		| [ ] -> [ ]
		| [ (spec, quotient_heap, quotient_preds, subst, pf_discharges) ] ->
			(* Printf.printf "this was a TOTAL MATCH!!!!\n"; *)
			transform_symb_state spec symb_state quotient_heap quotient_preds subst pf_discharges
	 	| _ :: _ ->
			(* Printf.printf "this was a PARTIAL MATCH!!!!\n"; *)
			let new_symb_states = List.map transform_symb_state_partial_match quotients in
			let new_symb_states = List.concat new_symb_states in
			new_symb_states in

	let quotients = find_correct_specs proc_specs.n_proc_specs [] in
	apply_correct_specs quotients



let fold_predicate pred_name pred_defs symb_state params args =

	(* create a new symb state with the abstract store in which the
	    called procedure is to be executed *)
	let new_store = JSIL_Logic_Normalise.init_store params args in
	let symb_state_aux = symb_state_replace_store symb_state new_store in

	let rec find_correct_pred_def pred_defs =
		(match pred_defs with
		| [] -> None
		| pred_def :: rest_pred_defs ->
			(* Printf.printf "Current pred symbolic state: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_state pred_def); *)
			let unifier = Structural_Entailment.unify_symb_states [] pred_def symb_state_aux in
			(match unifier with
			| Some (quotient_heap, quotient_preds, subst, pf_discharges, true) ->
			  (* Printf.printf "I can fold this!!!\n"; *)
				let symb_state = Symbolic_State_Functions.symb_state_replace_heap symb_state quotient_heap in
				let symb_state = Symbolic_State_Functions.symb_state_replace_preds symb_state quotient_preds in
				extend_symb_state_with_pfs symb_state pf_discharges;
				symb_state_add_predicate_assertion symb_state (pred_name, args);
				(* Printf.printf "Symbolic state after FOLDING:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state); *)
				Some symb_state

			| Some (_, _, _, _, false) ->
				find_correct_pred_def rest_pred_defs

			| None ->
				find_correct_pred_def rest_pred_defs)) in
	find_correct_pred_def pred_defs



let unfold_predicates pred_name pred_defs symb_state params args spec_vars =
	let subst0 = Symbolic_State_Functions.subtract_pred pred_name args (get_preds symb_state) (get_pf symb_state) (get_gamma symb_state) spec_vars in
	let args = List.map (fun le -> lexpr_substitution le subst0 true) args in
	let store = JSIL_Logic_Normalise.init_store params args in

	(* Printf.printf "I WILL BEGIN TO UNFOLD: NUMBER OF DEFINITIONS: %i\n" (List.length  pred_defs); *)

	let rec loop pred_defs (symb_states : symbolic_state list) =
		(match pred_defs with
		| [] -> symb_states
		| pred_symb_state :: rest_pred_defs ->
			let pat_subst = init_substitution [] in
			let subst = init_substitution [] in
			let pat_store = get_store pred_symb_state in
			(* Printf.printf "UNFOLD PREDICATES UNFOLD PREDICATES. Pat_store: %s Store: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_store pat_store false) (JSIL_Memory_Print.string_of_shallow_symb_store store false); *)
			let discharges = Structural_Entailment.unify_stores pat_store store pat_subst (Some subst) (pfs_to_list (get_pf symb_state)) (get_gamma symb_state) in
			(match discharges with
			| Some discharges ->
					(* Printf.printf "Current pred symbolic state: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_state pred_symb_state); *)
					(*Printf.printf "I need to apply the following subst in the current symbolic store: %s\n"
						(JSIL_Memory_Print.string_of_substitution subst);
					Printf.printf "I need to apply the following subst in the pattern symbolic store: %s\n"
						(JSIL_Memory_Print.string_of_substitution pat_subst); *)
					let new_symb_state : symbolic_state = copy_symb_state symb_state in
					let (new_symb_state : symbolic_state) = Symbolic_State_Functions.symb_state_substitution new_symb_state subst true in
					Symbolic_State_Functions.symb_state_add_subst_as_equalities new_symb_state subst (get_pf new_symb_state) spec_vars;
					(* Printf.printf "Symbolic state after substitution: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_state new_symb_state);
					Printf.printf "Pred Symb_sate:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state pred_symb_state);
					Printf.printf " subst: %s pat_subst: %s\n" (JSIL_Memory_Print.string_of_substitution subst) (JSIL_Memory_Print.string_of_substitution pat_subst); *)
					let pat_subst = compose_partial_substitutions subst pat_subst in
					let unfolded_symb_state = Symbolic_State_Functions.merge_symb_states new_symb_state pred_symb_state pat_subst in
					(* Printf.printf "pred symbolic state at the middle: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_state pred_symb_state); *)
					let spec_vars_subst = filter_substitution subst spec_vars in

					let pf = get_pf unfolded_symb_state in
					let gamma =  (get_gamma unfolded_symb_state) in
					let new_pfs = pf_of_substitution spec_vars_subst in
					let new_pfs_subst0 = pf_of_substitution subst0 in
					let pf_discharges = Structural_Entailment.pf_list_of_discharges discharges pat_subst in

					extend_pf pf new_pfs;
					extend_pf pf new_pfs_subst0;
					extend_pf pf pf_discharges;

					JSIL_Logic_Normalise.extend_typing_env_using_assertion_info new_pfs gamma;
					JSIL_Logic_Normalise.extend_typing_env_using_assertion_info new_pfs_subst0 gamma;
					JSIL_Logic_Normalise.extend_typing_env_using_assertion_info pf_discharges gamma;

					(* Printf.printf "The discharges to prove are: %s\n" (JSIL_Print.str_of_assertion_list pf_discharges); *)
					(* Printf.printf "I unfolded the following symbolic state:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state unfolded_symb_state); *)
					let satisfiability_check = Pure_Entailment.check_satisfiability (get_pf_list unfolded_symb_state) gamma [] in
					(* let discharges_check = Entailment_Engine.check_entailment [] pf pf_discharges gamma in *)
					if (satisfiability_check)
						then (
							(* Printf.printf "Checked the pure part of the unfolding!!\n"; *)
							loop rest_pred_defs (unfolded_symb_state :: symb_states))
						else (
							(* Printf.printf "Could NOT check the pure part of the unfolding. satisfiability_check: %b.\n" satisfiability_check;
							Printf.printf "pf_discharges: %s\n" (JSIL_Print.str_of_assertion_list pf_discharges); *)
							loop rest_pred_defs symb_states)
			| None -> loop rest_pred_defs symb_states)) in

	loop pred_defs []


let symb_evaluate_logic_cmd s_prog l_cmd symb_state subst spec_vars =

	let get_pred_data pred_name les =
		let pred = get_pred s_prog.pred_defs pred_name in
		let args =
			List.map
				(fun le -> JSIL_Logic_Normalise.normalise_lexpr (get_store symb_state) (get_gamma symb_state) subst le)
				les in
		let params = pred.n_pred_params in
		let pred_defs = pred.n_pred_definitions in
		(params, pred_defs, args) in

	match l_cmd with
	| Fold a ->
		(match a with
		| LPred	(pred_name, les) ->
			let params, pred_defs, args = get_pred_data pred_name les in
			let new_symb_state = fold_predicate pred_name pred_defs symb_state params args in
			(match new_symb_state with
			| Some symb_state ->
				(* Printf.printf "\n\nFOLDED SUCCESSFULLY!!!!\n\n\n"; *)
				[ symb_state ]
			| None ->
				Printf.printf "\nSTATE ON ERROR: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state);
				let msg = Printf.sprintf "Could not fold: %s " (JSIL_Print.string_of_logic_assertion a false) in
				raise (Failure msg))
		| _ ->
			let msg = Printf.sprintf "Illegal fold command %s" (JSIL_Print.string_of_logic_assertion a false) in
			raise (Failure msg))

	| Unfold a ->
		(match a with
		| LPred (pred_name, les) ->
			let params, pred_defs, args = get_pred_data pred_name les in
			unfold_predicates pred_name pred_defs symb_state params args spec_vars
		| _ ->
			let msg = Printf.sprintf "Illegal unfold command %s" (JSIL_Print.string_of_logic_assertion a false) in
			raise (Failure msg))


let rec symb_evaluate_logic_cmds s_prog (l_cmds : jsil_logic_command list) (symb_states : symbolic_state list) subst spec_vars =
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


let rec symb_evaluate_cmd s_prog proc spec search_info symb_state i =
	(* auxiliary functions *)
	let mark_as_visited search_info i =
		let cur_node_info = search_info.cur_node_info in
		Hashtbl.replace search_info.vis_tbl i cur_node_info.node_number in


	let print_symb_state_and_cmd () =
		let symb_state_str = JSIL_Memory_Print.string_of_shallow_symb_state symb_state in
		let cmd = get_proc_cmd proc i in
		let cmd_str = JSIL_Print.string_of_cmd cmd 0 0 false false false in
		Printf.printf
			"---------------------------------\n--%i--\nSTATE:\n%sCMD: %s\n----------------------------------\n"
			i symb_state_str cmd_str in

	(* symbolically evaluate a guarded goto *)
	let symb_evaluate_guarded_goto e j k =
		let le = symb_evaluate_expr e (get_store symb_state) (get_gamma symb_state) (get_pf symb_state) in
		let _, a_le = lift_logic_expr le in
		let a_le_then, a_le_else =
			match a_le with
			| Some a_le ->
				(* Printf.printf "Lifted assertion: %s\n" (JSIL_Print.string_of_logic_assertion a_le false); *)
				([ a_le ], [ (LNot a_le) ])
			| None -> ([], []) in

		if (Pure_Entailment.check_entailment [] (get_pf_list symb_state) a_le_then (get_gamma symb_state)) then
			(Printf.printf "in the THEN branch\n";
			symb_evaluate_next_cmd s_prog proc spec search_info symb_state i j)
			else (if (Pure_Entailment.check_entailment [] (get_pf_list symb_state) a_le_else (get_gamma symb_state)) then
					(Printf.printf "in the ELSE branch\n";
					symb_evaluate_next_cmd s_prog proc spec search_info symb_state i k)
				else
					(* Printf.printf "I could not determine the branch bla bla \n"; *)

					let then_symb_state = symb_state in
					let then_search_info = search_info in
					let else_symb_state = copy_symb_state symb_state in
					let else_search_info = update_vis_tbl search_info (copy_vis_tbl search_info.vis_tbl) in

					extend_symb_state_with_pfs then_symb_state a_le_then;
					symb_evaluate_next_cmd s_prog proc spec then_search_info then_symb_state i j;
					extend_symb_state_with_pfs else_symb_state a_le_else;
					symb_evaluate_next_cmd s_prog proc spec else_search_info else_symb_state i k) in


	(* symbolically evaluate a procedure call *)
	let symb_evaluate_call x e e_args j =

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
					symb_evaluate_next_cmd s_prog proc spec new_search_info symb_state i (i+1)
				| Error, None -> raise (Failure (Printf.sprintf "Procedure %s may return an error, but no error label was provided." proc_name))
				| Error, Some j ->
					symb_evaluate_next_cmd s_prog proc spec new_search_info symb_state i j))
			new_symb_states in


	if (!verbose) then print_symb_state_and_cmd ();
	let metadata, cmd = get_proc_cmd proc i in
	mark_as_visited search_info i;
	match cmd with
	| SBasic bcmd ->
		let _ = symb_evaluate_bcmd bcmd symb_state in
		symb_evaluate_next_cmd s_prog proc spec search_info symb_state i (i+1)

	| SGoto j -> symb_evaluate_next_cmd s_prog proc spec search_info symb_state i j

	| SGuardedGoto (e, j, k) -> symb_evaluate_guarded_goto e j k

	| SCall (x, e, e_args, j) -> symb_evaluate_call x e e_args j

	| _ -> raise (Failure "not implemented yet")

and symb_evaluate_next_cmd s_prog proc spec search_info symb_state cur next  =

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
						let new_symb_state, _ = JSIL_Logic_Normalise.normalise_postcondition a spec.n_subst spec.n_lvars in
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
							let new_symb_state, _ = JSIL_Logic_Normalise.normalise_postcondition a spec.n_subst spec.n_lvars in
							(match (Structural_Entailment.fully_unify_symb_state new_symb_state symb_state spec.n_lvars) with
							| Some _, _ -> new_symb_state
							| None, msg -> raise (Failure msg)) in


					let symb_states = symb_evaluate_logic_cmds s_prog metadata.logic_cmds [ symb_state ] spec.n_subst spec.n_lvars in
					(* Printf.printf "I unfolded everything that needed to be unfolded!!!!\n"; *)
					let len = List.length symb_states in
					List.iter
						(fun symb_state ->
							let vis_tbl = if (len > 1) then (copy_vis_tbl search_info.vis_tbl) else search_info.vis_tbl in
							let info_node = Symbolic_Traces.create_info_node_from_cmd search_info symb_state cmd next in
							let new_search_info = udpdate_search_info search_info info_node vis_tbl in
							symb_evaluate_cmd s_prog proc spec new_search_info symb_state next)
						symb_states
				end
		end)


let symb_evaluate_proc s_prog proc_name spec i prunning_info =
	let node_info = Symbolic_Traces.create_info_node_aux spec.n_pre 0 (-1) "Precondition" in
	let search_info = make_symb_exe_search_info node_info prunning_info i in

	let proc = get_proc s_prog.program proc_name in
	let sep_str = "---------------------------------------------------\n" in

	if (!verbose) then Printf.printf "%s" (sep_str ^ sep_str ^ sep_str ^ "Symbolic execution of " ^ proc_name ^ "\n");
	let success, failure_msg =
		(try
			symb_evaluate_next_cmd s_prog proc spec search_info spec.n_pre (-1) 0;
			true, None
		with Failure msg ->
			(Printf.printf "The EVALUATION OF THIS PROC GAVE AN ERROR: %d %s!!!!\n" i msg;
			Symbolic_Traces.create_info_node_from_error search_info msg;
			Symbolic_Traces.create_info_node_from_post search_info spec.n_post spec.n_ret_flag false;
			false, Some msg)) in
	let proc_name = Printf.sprintf "Spec_%d_of_%s" i proc_name in
	let search_dot_graph = JSIL_Memory_Print.dot_of_search_info search_info proc_name in
	(if (!verbose) then Printf.printf "%s" (sep_str ^ sep_str ^ sep_str));
	search_dot_graph, success, failure_msg



let sym_run_procs spec_table prog which_pred pred_defs =
	let n_pred_defs = JSIL_Logic_Normalise.normalise_predicate_definitions pred_defs in
	let s_prog = {
		program = prog;
		which_pred = which_pred;
		spec_tbl = spec_table;
		pred_defs = n_pred_defs
	} in
	let prunning_info = init_post_prunning_info () in
	let results = Hashtbl.fold
		(fun proc_name spec ac_results ->
			update_post_prunning_info_with_spec prunning_info spec;
			let pre_post_list = spec.n_proc_specs in
			let results = List.mapi
				(fun i pre_post ->
					let new_pre_post = copy_single_spec pre_post in
					let dot_graph, success, failure_msg = symb_evaluate_proc s_prog proc_name new_pre_post i prunning_info in
					(proc_name, i, pre_post, success, failure_msg, dot_graph))
				pre_post_list in
			let new_spec = { spec with n_proc_specs = (filter_useless_posts_in_multiple_specs proc_name pre_post_list prunning_info) } in
			Hashtbl.replace spec_table proc_name new_spec;
			ac_results @ results)
		spec_table
		[] in
	let complete_success =
		List.fold_left
			(fun ac (_, _, _, partial_success, _, _) ->
				if (ac && partial_success) then true else false)
			true
			results in
	let results_str, dot_graphs = JSIL_Memory_Print.string_of_symb_exe_results results in
	results_str, dot_graphs, complete_success
