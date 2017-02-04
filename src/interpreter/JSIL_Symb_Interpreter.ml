open JSIL_Syntax
open JSIL_Memory_Model
open JSIL_Logic_Utils
open Symbolic_State_Basics

let js = ref false

let print_le = (fun x -> JSIL_Print.string_of_logic_expression x false)

(**********************)
(* Symbolic Execution *)
(**********************)

(* List length, when possible *)
let rec get_list_length (le : jsil_logic_expr) : int option =
(match le with
	| LLit (LList list) -> Some (List.length list)
	| LEList list       -> Some (List.length list)
	| LBinOp (el, LstCons, llist) ->
		let len_llist = get_list_length llist in
		if_some len_llist (fun len -> Some (len + 1)) None
	| _ -> None)

(*******************************************)
(* Symbolic evaluation of JSIL expressions *)
(*******************************************)
let rec symb_evaluate_expr (store : symbolic_store) (gamma : typing_environment) (pure_formulae : pure_formulae) (expr : jsil_expr) : jsil_logic_expr =
let f = symb_evaluate_expr store gamma pure_formulae in
	match expr with
	(* Literals: Return the literal *)
	| Literal lit -> LLit lit

  (* Variables: 
	     a) If a variable is already in the store, return the variable
			 b) Otherwise, add a fresh logical variable (of the appropriate type) to the store and then return it *)
	| Var x ->
		let x_val = store_get_var_val store x in
		if_some_val_lazy x_val (lazy (extend_abs_store x store gamma))

  (* Binary operators:
	     a) if both operands evaluate to literals, execute the operator and return the result
	     b) otherwise, if the operator is equality and the types of the operands are not equal, return false
			 c) otherwise, return the lifted binary operator *)
	| BinOp (e1, op, e2) ->
		let nle1 = f e1 in
		let nle2 = f e2 in
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
					| Some t1, Some t2 -> if (t1 = t2) then LBinOp (nle1, op, nle2) else (LLit (Bool false)) 
					| _, _             -> LBinOp (nle1, op, nle2))
			| _ -> LBinOp (nle1, op, nle2)))

  (* Unary operators
	     a) if the operand evaluates to a literal, execute the operator and return the result
			 b) otherwise, if the operator is Cdr, try to calculate the tail of the list and return it
			 c) otherwise, if the operator is LstLen, try to calculate the length of the list and return it
			 d) otherwise, return the lifted unary operator *)
	| UnOp (op, e) ->
		let nle = f e in
		(match nle with
 	  | LLit lit -> 
			let l = JSIL_Interpreter.evaluate_unop op lit in
				LLit l
		| _ ->
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
				let len = get_list_length nle in
					if_some len (fun len -> LLit (Integer len)) (LUnOp (op, nle))
			| _ -> LUnOp (op, nle)))

  (* TypeOf:
	     a) if the parameter is typable in the typing environment, return the type
			 b) otherwise, return the lifted typeOf *)
	| TypeOf (e) ->
		let nle = f e in
		let nle_type, _, _ = type_lexpr gamma nle in
		if_some nle_type (fun t -> LLit (Type t)) (LTypeOf (nle))

  (* List of expressions: Evaluate all elements and then
	     a) If all are literals, convert to a literal list
			 b) Otherwise, return the lifted list of logical expressions
  *)
	| EList es ->
		let les = List.map (fun e -> f e) es in
		let rec loop les lits =
			(match les with
			| [] -> true, lits
			| le :: rest ->
				(match le with
				| LLit l -> loop rest (l :: lits)
				| _ -> false, [])) in
		let all_literals, lits = loop les [] in
		if all_literals
			then 
				let lits = List.rev lits in
					LLit (LList lits)
			else LEList les

  (* List n-th: Evaluate the list and the index
	     a) Attempt to reduce fully, if possible, return the result
			 b) Otherwise, return the lifted list n-th
  *)
	| LstNth (e1, e2) ->
		let list = f e1 in
		let index = f e2 in
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

  (* List n-th: Evaluate the string and the index
	     a) Attempt to reduce fully, if possible, return the result
			 b) Otherwise, return the lifted string n-th
  *)
	| StrNth (e1, e2) ->
		let str = f e1 in
		let index = f e2 in
		let index =
			(match index with
			| LLit (Num n) -> LLit (Integer (int_of_float n))
			| _ -> index) in
		(match index with
		| LLit (Integer n) ->
		 	if (n < 0) then raise (Failure "String index negative.")
			else
				(match str with
				| LLit (String s) -> LLit (String (String.make 1 (String.get s n)))
				| _ -> LStrNth (str, index))
		| _ -> LStrNth (str, index))

(************************************************)
(* SAFE Symbolic evaluation of JSIL expressions *)
(************************************************)
(* 
	a) If the result of the evaluation is typable, then any constraints produced by typing must also make sense
	b) Otherwise, variables are allowed to stay untyped
	c) Otherwise, an error is thrown 
*)
let safe_symb_evaluate_expr store gamma pure_formulae (expr : jsil_expr) =
	let nle = symb_evaluate_expr store gamma pure_formulae expr in
	let nle_type, is_typable, constraints = type_lexpr gamma nle in
	let is_typable = is_typable && ((List.length constraints = 0) || (Pure_Entailment.old_check_entailment [] (pfs_to_list pure_formulae) constraints gamma)) in
	if (is_typable) then
		nle, nle_type, true
	else
		(match nle with
		| LVar _ ->  nle, None, false
		| _ ->
				let gamma_str = JSIL_Memory_Print.string_of_gamma gamma in
				let pure_str = JSIL_Memory_Print.string_of_shallow_p_formulae pure_formulae false in
				let msg = Printf.sprintf "The logical expression %s is not typable in the typing enviroment: %s \n with the pure formulae %s" (print_le nle) gamma_str pure_str in
				raise (Failure msg))

(**********************************************)
(* Symbolic evaluation of JSIL basic commands *)
(**********************************************)
let symb_evaluate_bcmd bcmd (symb_state : symbolic_state) =
	let heap, store, pure_formulae, gamma, _ = symb_state in
	let ssee = safe_symb_evaluate_expr store gamma pure_formulae in
	match bcmd with
	(* Skip: skip;
			Always return $$empty *)
	| SSkip ->
		LLit Empty

  (* Assignment: x = e;
			a) Safely evaluate e to obtain nle and its type tle
			b) Update the abstract store with [x |-> nle]
			c) Update the typing environment with [x |-> tle] 
			d) Return nle *)
	| SAssignment (x, e) ->
		let nle, tle, _ = ssee e in
		update_abs_store store x nle;
		update_gamma gamma x tle;
		nle

	(* Object creation: x = new ();
			a) Create fresh object location #l and add it to the heap
			b) Set (#l, "@proto") -> $$null in the heap
			c) Update the abstract store with [x |-> #l]
			d) Update the typing environment with [x |-> $$object_type]
			e) Add the fact that the new location is not $lg to the pure formulae
			f) Return the new location
	*)
	| SNew x ->
		let new_loc = fresh_aloc () in
		Symbolic_State_Functions.update_abs_heap_default heap new_loc LNone;
		Symbolic_State_Functions.update_abs_heap heap new_loc (LLit (String (Js2jsil_constants.internalProtoFieldName))) (LLit Null) pure_formulae (* solver *) gamma;
		update_abs_store store x (ALoc new_loc);
		update_gamma gamma x (Some ObjectType);
		DynArray.add pure_formulae (LNot (LEq (ALoc new_loc, LLit (Loc Js2jsil_constants.locGlobName))));
		ALoc new_loc

  (* Property lookup: x = [e1, e2];
			a) Safely evaluate e1 to obtain the object location ne1 and its type te1
			b) Safely evaluate e2 to obtain the property name ne2 and its type te2
			c) If ne1 is not a literal location or an abstract location, throw an error
			d) Otherwise, try to find the value ne of the property ne2 of object ne1
			e) If successful, update the store with [x |-> ne]
			f) Return ne
	*)
	| SLookup (x, e1, e2) ->
		let ne1, te1, _ = ssee e1 in
		let ne2, te2, _ = ssee e2 in
		let l =
			(match ne1 with
			| LLit (Loc l)
			| ALoc l -> l
			| _ -> raise (Failure (Printf.sprintf "Lookup: I do not know which location %s denotes in the symbolic heap" (print_le ne1)))) in
		let ne = Symbolic_State_Functions.abs_heap_find heap l ne2 pure_formulae gamma in
		update_abs_store store x ne;
		ne

  (* Property assignment: [e1, e2] := e3;
			a) Safely evaluate e1 to obtain the object location ne1 and its type te1
			b) Safely evaluate e2 to obtain the property name ne2 and its type te2
			c) Safely evaluate e3 to obtain the value ne3 to be assigned
			d) If ne1 is not a literal location or an abstract location, throw an error
			e) Update the heap with (ne1, ne2) -> ne3
			f) Return ne3
	*)
	| SMutation (e1, e2, e3) ->
		let ne1, t_le1, _ = ssee e1 in
		let ne2, t_le2, _ = ssee e2 in
		let ne3, _, _ = ssee e3 in
		(match ne1 with
		| LLit (Loc l)
		| ALoc l ->
			Symbolic_State_Functions.update_abs_heap heap l ne2 ne3 pure_formulae gamma
		| _ -> raise (Failure (Printf.sprintf "Mutation: I do not know which location %s denotes in the symbolic heap" (print_le ne1))));
		ne3

  (* Property deletion: delete(e1, e2)
			a) Safely evaluate e1 to obtain the object location ne1 and its type te1
			b) Safely evaluate e2 to obtain the property name ne2 and its type te2
			c) If ne1 is not a literal location or an abstract location, throw an error
			e) Delete (ne1, ne2) from the heap
			f) Return true
	*)
	| SDelete (e1, e2) ->
		let ne1, t_le1, _ = ssee e1 in
		let ne2, t_le2, _ = ssee e2 in
		let l =
			(match ne1 with
			| LLit (Loc l)
			| ALoc l -> l
			| _ -> raise (Failure (Printf.sprintf "Delete: I do not know which location %s denotes in the symbolic heap" (print_le ne1)))) in
		Symbolic_State_Functions.update_abs_heap heap l ne2 LNone pure_formulae gamma;
		LLit (Bool true)

  (* Object deletion: deleteObj(e1)
			a) Safely evaluate e1 to obtain the object location ne1 and its type te1
			b) If ne1 is not a literal location or an abstract location, throw an error
			c) If the object at ne1 does not exist in the heap, throw an error
			c) Delete the entire object ne1 from the heap
			d) Return true
	*)
	| SDeleteObj e1 ->
		let ne1, t_le1, _ = ssee e1 in
		let l =
			(match ne1 with
			| LLit (Loc l)
			| ALoc l -> l
			| _ -> raise (Failure (Printf.sprintf "DeleteObject: I do not know which location %s denotes in the symbolic heap" (print_le ne1)))) in
		(match (LHeap.mem heap l) with
		 | false -> raise (Failure (Printf.sprintf "Attempting to delete an inexistent object: %s" (print_le ne1)))
		 | true -> LHeap.remove heap l; LLit (Bool true));

  (* Property existence: x = hasField(e1, e2);
			a) Safely evaluate e1 to obtain the object location ne1 and its type te1
			b) Safely evaluate e2 to obtain the property name ne2 and its type te2
			c) If ne1 is not a literal location or an abstract location, throw an error
			d) Otherwise, understand if the object ne1 has the property ne2 and store that result in res;
			e) If conclusive, update the store with [x |-> res] and return res
			f) Otherwise, return unknown
			e) If successful, update the store with [x |-> ne]
			f) Return ne
	*)
	| SHasField (x, e1, e2) ->
		let ne1, t_le1, _ = ssee e1 in
		let ne2, t_le2, _ = ssee e2 in
		match ne1 with
		| LLit (Loc l)
		| ALoc l ->
				let res = Symbolic_State_Functions.abs_heap_check_field_existence heap l ne2 pure_formulae gamma in
				update_gamma gamma x (Some BooleanType);
				if_some res (fun res -> 
					let res_lit = LLit (Bool res) in
					update_abs_store store x res_lit;
					res_lit) LUnknown
		| _ -> raise (Failure (Printf.sprintf "HasField: I do not know which location %s denotes in the symbolic heap" (print_le ne1)))


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
	print_debug (Printf.sprintf ("\nFOLDING %s(%s) with the existentials %s in the symbolic state: \n%s\n")
	  pred_name 
		(String.concat ", " (List.map (fun le -> JSIL_Print.string_of_logic_expression le false) args))
		existentials_str
		(JSIL_Memory_Print.string_of_shallow_symb_state symb_state));

	let update_symb_state_after_folding complete_fold symb_state quotient_heap quotient_preds new_pfs new_gamma pred_name args =
		print_time_debug ("update_symb_state_after_folding:");
		let symb_state = symb_state_replace_heap symb_state quotient_heap in
		let symb_state = symb_state_replace_preds symb_state quotient_preds in
		let symb_state = symb_state_replace_gamma symb_state new_gamma in
		extend_symb_state_with_pfs symb_state (DynArray.of_list new_pfs);
		(* if complete_fold then symb_state_add_predicate_assertion symb_state (pred_name, args); *)
		symb_state in

	let rec find_correct_pred_def cur_pred_defs =
		print_time_debug ("find_correct_pred_def:");
		(match cur_pred_defs with
		| [] -> None
		| pred_def :: rest_pred_defs ->
			print_debug (Printf.sprintf "----------------------------");
			print_debug (Printf.sprintf "Current pred symbolic state: %s" (JSIL_Memory_Print.string_of_shallow_symb_state pred_def));
			let unifier = Structural_Entailment.unify_symb_states_fold pred_name existentials pred_def symb_state_aux in
			(match unifier with
			| Some (true, quotient_heap, quotient_preds, subst, pf_discharges, new_gamma, _, []) ->
			  print_debug (Printf.sprintf "I can fold this!!!");
				let new_symb_state = update_symb_state_after_folding true symb_state quotient_heap quotient_preds pf_discharges new_gamma pred_name args in
				print_debug (Printf.sprintf "Symbolic state after FOLDING:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state new_symb_state));
				Some new_symb_state

			| Some (true, quotient_heap, quotient_preds, subst, pf_discharges, new_gamma, existentials, [ (missing_pred_name, missing_pred_args) ]) ->
				let missing_pred_args = List.map (fun le -> JSIL_Logic_Utils.lexpr_substitution le subst false) missing_pred_args in
				if (not (missing_pred_name = pred_name)) then None else (
					print_debug (Printf.sprintf "I can NOT quite fold this because I am missing %s(%s)!!!"
						missing_pred_name
						(String.concat ", " (List.map (fun le -> JSIL_Print.string_of_logic_expression le false) missing_pred_args)));
					let new_symb_state = update_symb_state_after_folding false symb_state quotient_heap quotient_preds pf_discharges new_gamma pred_name args in
					let new_symb_state, new_subst = simplify_with_subst true new_symb_state in
					print_debug (Printf.sprintf "New subst: %d \n%s" (List.length new_subst) (String.concat "\n" (List.map (fun (x, le) -> Printf.sprintf "   (%s, %s)" x (JSIL_Print.string_of_logic_expression le false)) new_subst)));
					let existentials_to_remove = (List.map (fun (v, _) -> v) new_subst) in 
					print_debug (Printf.sprintf "Exists to remove: %s" (String.concat "," existentials_to_remove));
					print_debug (Printf.sprintf "Old exists: %s" (String.concat "," existentials));
					let new_existentials = List.filter (fun v -> (not (List.mem v existentials_to_remove))) existentials in 
					print_debug (Printf.sprintf "New exists: %s" (String.concat "," new_existentials));
					let new_subst = JSIL_Logic_Utils.init_substitution3 new_subst in 
					print_debug (Printf.sprintf "New substitution: \n%s" (JSIL_Memory_Print.string_of_substitution new_subst));
					let missing_pred_args = List.map (fun le -> JSIL_Logic_Utils.lexpr_substitution le new_subst true) missing_pred_args in
					print_debug (Printf.sprintf "And now I am missing %s(%s)!!!"
						missing_pred_name
						(String.concat ", " (List.map (fun le -> JSIL_Print.string_of_logic_expression le false) missing_pred_args)));
					(* let subst = resolve_existentials (get_pf new_symb_state) existentials in 
					let new_symb_state = Symbolic_State_Basics.symb_state_substitution new_symb_state subst true in *)
					print_debug (Printf.sprintf "Symbolic state after partial FOLDING:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state new_symb_state));
					let new_symb_state = fold_predicate pred_name pred_defs new_symb_state params missing_pred_args (Some new_existentials) in
					(match new_symb_state with
					| Some new_symb_state ->
						(* remove_predicate_assertion (get_preds new_symb_state) (missing_pred_name, missing_pred_args); *) 
						Some new_symb_state
					| None -> None))

			| Some (_, _, _, _, _, _, _, _) | None -> find_correct_pred_def rest_pred_defs)) in
	find_correct_pred_def pred_defs

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
				symb_state_add_predicate_assertion symb_state (pred_name, args);
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
			else symb_evaluate_logic_cmds s_prog else_lcmds [ symb_state ] subst spec_vars 
		
	| Macro (name, param_vals) ->
			let actual_command = unfold_macro name param_vals in 
			(* print_debug (Printf.sprintf ("Unfolded macro: %s(%s) -> %s") 
				name
				(String.concat ", " (List.map (fun x -> JSIL_Print.string_of_logic_expression x false) param_vals))
				(JSIL_Print.string_of_lcmd actual_command)); *)
					symb_evaluate_logic_cmd s_prog actual_command symb_state subst spec_vars
	)
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
		let le = symb_evaluate_expr (get_store symb_state) (get_gamma symb_state) (get_pf symb_state) e in
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
			symb_evaluate_next_cmd s_prog proc spec search_info symb_state i j)
			else (if (Pure_Entailment.old_check_entailment [] (get_pf_list symb_state) a_le_else (get_gamma symb_state)) then
					(print_endline "in the ELSE branch";
					symb_evaluate_next_cmd s_prog proc spec search_info symb_state i k)
				else
					(print_endline "I could not determine the branch.";

					let then_symb_state = symb_state in
					let then_search_info = search_info in
					let else_symb_state = copy_symb_state symb_state in
					let else_search_info = update_vis_tbl search_info (copy_vis_tbl search_info.vis_tbl) in

					extend_symb_state_with_pfs then_symb_state (DynArray.of_list a_le_then);
					symb_evaluate_next_cmd s_prog proc spec then_search_info then_symb_state i j;
					extend_symb_state_with_pfs else_symb_state (DynArray.of_list a_le_else);
					symb_evaluate_next_cmd s_prog proc spec else_search_info else_symb_state i k)) in


	(* symbolically evaluate a procedure call *)
	let symb_evaluate_call symb_state x e e_args j =

		(* get the name and specs of the procedure being called *)
		let le_proc_name = symb_evaluate_expr (get_store symb_state) (get_gamma symb_state) (get_pf symb_state) e in
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
		let le_args = List.map (fun e -> symb_evaluate_expr (get_store symb_state) (get_gamma symb_state) (get_pf symb_state) e) e_args in
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

	(* symbolically evaluate a phi command *)
	let symb_evaluate_phi symb_state x x_arr =
		let cur_proc_name = proc.proc_name in
		let cur_which_pred =
			try Hashtbl.find s_prog.which_pred (cur_proc_name, prev, i)
			with _ ->  raise (Failure (Printf.sprintf "which_pred undefined for command: %s %d %d" cur_proc_name prev i)) in
		let expr = x_arr.(cur_which_pred) in
		let le = symb_evaluate_expr (get_store symb_state) (get_gamma symb_state) (get_pf symb_state) expr in
		let te, _, _ =	type_lexpr (get_gamma symb_state) le in
		update_abs_store (get_store symb_state) x le;
		update_gamma (get_gamma symb_state) x te;
		symb_evaluate_next_cmd s_prog proc spec search_info symb_state i (i+1) in

	let symb_state = simplify false symb_state in
	print_symb_state_and_cmd symb_state;
	let metadata, cmd = get_proc_cmd proc i in
	mark_as_visited search_info i;
	match cmd with
	| SBasic bcmd ->
		let _ = symb_evaluate_bcmd bcmd symb_state in
		symb_evaluate_next_cmd s_prog proc spec search_info symb_state i (i+1)

	| SGoto j -> symb_evaluate_next_cmd s_prog proc spec search_info symb_state i j

	| SGuardedGoto (e, j, k) -> symb_evaluate_guarded_goto symb_state e j k

	| SCall (x, e, e_args, j) -> symb_evaluate_call symb_state x e e_args j

	| SPhiAssignment (x, x_arr) -> symb_evaluate_phi symb_state x x_arr

	| _ -> raise (Failure "not implemented yet")

(**
	Symbolically evaluate the next command of the program
	
	@param s_prog      Extended JSIL program
	@param proc        The procedure that is being executed
	@param spec        The specification to be verified
	@param search_info Something for the dot graphs
	@param symb_state  Current symbolic state
	@param cur         Index of the current command
	@param next        Index of the next command
	
	@return symb_states The list of symbolic states resulting from the evaluation
*)
and symb_evaluate_next_cmd s_prog proc spec search_info symb_state cur next  =
	(* Get the current command and the associated metadata *)
	let metadata, cmd = get_proc_cmd proc cur in
	(* Evaluate logic commands, if any *)
	let symb_states = symb_evaluate_logic_cmds s_prog metadata.post_logic_cmds [ symb_state ] spec.n_subst spec.n_lvars in
	(* The number of symbolic states resulting from the evaluation of the logic commands *)
	let len = List.length symb_states in
	(* For each obtained symbolic state *) 
	List.iter
		(* Get the symbolic state *)
		(fun symb_state ->
			let search_info =
				if (len > 1)
					then { search_info with vis_tbl = (copy_vis_tbl search_info.vis_tbl) }
					else search_info in
				(* Go bravely into the continuation *)
				symb_evaluate_next_cmd_cont s_prog proc spec search_info symb_state cur next)
		symb_states

(**
	Continuation of symbolic evaluation of the next command of the program
	
	@param s_prog      Extended JSIL program
	@param proc        The procedure that is being executed
	@param spec        The specification to be verified
	@param search_info Something for the dot graphs
	@param symb_state  Current symbolic state
	@param cur         Index of the current command
	@param next        Index of the next command
	
	@return symb_states The list of symbolic states resulting from the evaluation
*)
and symb_evaluate_next_cmd_cont s_prog proc spec search_info symb_state cur next  =

  (* i1: Has the current command already been visited? *)
  let is_visited i = Hashtbl.mem search_info.vis_tbl i in

	(* Conclusion *)
	let finish how = 
		Structural_Entailment.unify_symb_state_against_post proc.proc_name spec symb_state how search_info !js;
		Symbolic_Traces.create_info_node_from_post search_info spec.n_post how true; () in
	
	(* i2: Have we reached the return label? *)
	if (Some cur = proc.ret_label) then
		(* i2: YES: Unify the final symbolic state against the postcondition *)
		finish Normal
	(* i2: NO: Have we reached the error label? *)
	else (if (Some cur = proc.error_label) then
		(* i3: YES: Unify the final symbolic state against the postcondition *)
		finish Error
	(* i3: NO: The control did not reach the end of the symbolic execution *)
	else
		begin
			(* Get the next command and its metadata *)
			let metadata, cmd = get_proc_cmd proc next in
			(* i1: YES: We have visited the current command and are in a loop *)
			if (is_visited next) then
				begin
					(* Get the invariant *)
					match (metadata.invariant) with
					(* No invariant, throw an error *)
					| None -> raise (Failure "back edges need to point to commands annotated with invariants")
					(* Invariant present, check if the current symbolic state entails the invariant *)
					| Some a ->
						(* check if the current symbolic state entails the invariant *)
						Printf.printf "MARICA, NO ME ABUSES MAS LOOP: I found an invariant: %s\n" (JSIL_Print.string_of_logic_assertion a false); 
						let new_symb_state, _ = JSIL_Logic_Normalise.normalise_postcondition a spec.n_subst spec.n_lvars (get_gamma spec.n_pre) in
						let new_symb_state, _ = simplify_for_your_legacy (DynArray.create()) new_symb_state in
						(match (Structural_Entailment.fully_unify_symb_state new_symb_state symb_state spec.n_lvars !js) with
						| Some _, _ -> ()
						| None, msg -> raise (Failure msg))
				end
			else
				(* i1: NO: We have not visited the current command *)
				begin
					(* Understand the symbolic state *)
					let symb_state =
						(* Get the invariant *)
						match (metadata.invariant) with
						(* No invariant, proceed *)
						| None -> symb_state
						(* Invariant present, check if the current symbolic state entails the invariant *)
						| Some a ->
							Printf.printf "MARICA. NO ME ABUSES MAS NO LOOP: I found an invariant: %s\n" (JSIL_Print.string_of_logic_assertion a false); 
							let new_symb_state, _ = JSIL_Logic_Normalise.normalise_postcondition a spec.n_subst spec.n_lvars (get_gamma spec.n_pre) in
							let new_symb_state, _ = simplify_for_your_legacy (DynArray.create()) new_symb_state in
							(match (Structural_Entailment.fully_unify_symb_state new_symb_state symb_state spec.n_lvars !js) with
							(* If it does, replace current symbolic state with the invariant *)
							| Some _, _ -> new_symb_state
							| None, msg -> raise (Failure msg)) in

					(* Evaluate logic commands, if any *)
					let symb_states = symb_evaluate_logic_cmds s_prog metadata.pre_logic_cmds [ symb_state ] spec.n_subst spec.n_lvars in
					(* The number of symbolic states resulting from the evaluation of the logic commands *)
					let len = List.length symb_states in
					(* For each obtained symbolic state *) 
					List.iter
						(* Get the symbolic state *)
						(fun symb_state ->
							(* Construct the search info for the next command *)
							let vis_tbl = if (len > 1) then (copy_vis_tbl search_info.vis_tbl) else search_info.vis_tbl in
							let info_node = Symbolic_Traces.create_info_node_from_cmd search_info symb_state cmd next in
							let new_search_info = update_search_info search_info info_node vis_tbl in
							(* Actually evaluate the next command *) 
							symb_evaluate_cmd s_prog proc spec new_search_info symb_state next cur)
						symb_states
				end
		end)

(**
	Symbolic execution of a JSIL procedure
	
	@param s_prog       Extended JSIL program
	@param proc_name    Name of the procedure
	@param spec         The specification to be verified
	@param i            Index of the current specification
	@param pruning_info Pruning information
	
	@return search_dot_graph The dot graph of the symbolic execution
	@return success          Success indicator
	@return failure_msg      Error message in case of failure
*)
let symb_evaluate_proc s_prog proc_name spec i pruning_info =
	let sep_str = "----------------------------------\n" in
	print_endline (Printf.sprintf "%s" (sep_str ^ sep_str ^ "Symbolic execution of " ^ proc_name));

	let node_info = Symbolic_Traces.create_info_node_aux spec.n_pre 0 (-1) "Precondition" in
	let search_info = make_symb_exe_search_info node_info pruning_info i in

	(* Get the procedure to be symbolically executed *)
	let proc = get_proc s_prog.program proc_name in
	let success, failure_msg =
		(try
			print_debug (Printf.sprintf "Initial symbolic state:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state spec.n_pre));
			let symb_state = copy_symb_state spec.n_pre in
			(* Symbolically execute the procedure *)
			symb_evaluate_next_cmd_cont s_prog proc spec search_info symb_state (-1) 0;
			(* Symbolic execution was successful *)
			true, None
		(* An error occurred during the symbolic execution *)
		with Failure msg ->
			(print_endline (Printf.sprintf "The EVALUATION OF THIS PROC GAVE AN ERROR: %d %s!!!!" i msg);
			Symbolic_Traces.create_info_node_from_error search_info msg;
			Symbolic_Traces.create_info_node_from_post search_info spec.n_post spec.n_ret_flag false;
			false, Some msg)) in
	let proc_name = Printf.sprintf "Spec_%d_of_%s" i proc_name in
	(* Create the dot graph of the symbolic execution *)
	let search_dot_graph = Some (JSIL_Memory_Print.dot_of_search_info search_info proc_name) in
	print_debug (Printf.sprintf "%s" (sep_str ^ sep_str ^ sep_str));
	(* Return *)
	search_dot_graph, success, failure_msg

(** 
	Symbolic execution of a given set of JSIL procedures

	@param prog            JSIL program 
	@param procs_to_verify The list of procedures of the JSIL program to be symbolically verified
	@param spec_table      The table of specifications associated with the JSIL program
	@param which_pred      The predecessor graph
	@param pred_defs       Predicate definitions
	
	@return results_str      Symbolic execution in string format
	@return dot_graphs       Dot graph of the symbolic execution
	@return complete_success Indicator of complete success
	
	TODO: Construct call graph, do dfs, do in that order
*)
let sym_run_procs prog procs_to_verify spec_table which_pred pred_defs =
	Macros.setup_internal_macros ();
	(* Normalise predicate definitions *)
	let n_pred_defs = JSIL_Logic_Normalise.normalise_predicate_definitions pred_defs in
	(* Construct corresponding extended JSIL program *)
	let s_prog = {
		program = prog;
		which_pred = which_pred;
		spec_tbl = spec_table;
		pred_defs = n_pred_defs
	} in
	let pruning_info = init_post_pruning_info () in
	(* Iterate over the specification table *)
	let results = Hashtbl.fold
	  (* For each specification: *)
		(fun proc_name spec ac_results ->
			(* i1: Should the procedure be verified? *)
			let should_we_verify = (Hashtbl.mem procs_to_verify proc_name) in
			(* i1: YES *)
			if (should_we_verify) then
			begin
				update_post_pruning_info_with_spec pruning_info spec;
				(* Get list of pre-post pairs *)
				let pre_post_list = spec.n_proc_specs in
				(* Iterate over the pre-post pairs *)
				let results =
					List.mapi
					(* For each pre-post pair *)
					(fun i pre_post ->
						let new_pre_post = Symbolic_State_Functions.copy_single_spec pre_post in
						(* Symbolically execute the procedure given the pre and post *)
						let dot_graph, success, failure_msg = symb_evaluate_proc s_prog proc_name new_pre_post i pruning_info in
						(proc_name, i, pre_post, success, failure_msg, dot_graph))
					pre_post_list in
				(* Filter specs that could not be verified *)
				let new_spec = { spec with n_proc_specs = (filter_useless_posts_in_multiple_specs proc_name pre_post_list pruning_info) } in
				(* Update the specification table *)
				Hashtbl.replace spec_table proc_name new_spec;
				(* Concatenate symbolic trace *)
				ac_results @ results
			end
			(* i1: NO *)
			else ac_results)
		spec_table
		[] in
	(* Understand complete success *)
	let complete_success =
		List.fold_left
			(fun ac (_, _, _, partial_success, _, _) ->
				if (ac && partial_success) then true else false)
			true
			results in
	(* Get the string and dot graphs of the symbolic execution *)
	let results_str, dot_graphs = JSIL_Memory_Print.string_of_symb_exe_results results in
	(* Some statistics *)
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
	(* Return *)
	results_str, dot_graphs, complete_success
