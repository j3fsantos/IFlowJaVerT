open DynArray
open Set
open Stack
open JSIL_Syntax
open Symbolic_State
open JSIL_Logic_Utils
open Logic_Predicates

(**
	le -> non - normalised logical expression
	subst -> table mapping variable and logical variable
	gamma -> table mapping logical variables + variables to types

	the store is assumed to contain all the program variables in le
*)
let rec normalise_lexpr store gamma subst le =

	let start_time = Sys.time() in

	let f = normalise_lexpr store gamma subst in

	try (
	let result = match le with
	| LLit _
	| LUnknown
	| LNone -> le
	| LVar lvar -> (try Hashtbl.find subst lvar with _ -> LVar lvar)
	| ALoc aloc -> ALoc aloc (* raise (Failure "Unsupported expression during normalization: ALoc") Why not ALoc aloc? *)
	| PVar pvar ->
		(try Hashtbl.find store pvar with
		| _ ->
			let new_lvar = extend_abs_store pvar store gamma in
			Hashtbl.add subst pvar new_lvar;
			new_lvar)

	| LBinOp (le1, bop, le2) ->
		let nle1 = f le1 in
		let nle2 = f le2 in
		(match nle1, nle2 with
			| LLit lit1, LLit lit2 ->
				let lit = JSIL_Interpreter.evaluate_binop bop (Literal lit1) (Literal lit2) (Hashtbl.create 1) in
					LLit lit
			| _, _ -> LBinOp (nle1, bop, nle2))

	| LUnOp (uop, le1) ->
		let nle1 = f le1 in
		(match nle1 with
			| LLit lit1 ->
				let lit = JSIL_Interpreter.evaluate_unop uop lit1 in
				LLit lit
			| _ -> LUnOp (uop, nle1))

	| LTypeOf (le1) ->
		let nle1 = f le1 in
		(match nle1 with
			| LUnknown -> raise (Failure "Illegal Logic Expression: TypeOf of Unknown")
			| LLit llit -> LLit (Type (evaluate_type_of llit))
			| LNone -> raise (Failure "Illegal Logic Expression: TypeOf of None")
			| LVar lvar ->
				(try LLit (Type (Hashtbl.find gamma lvar)) with _ -> LTypeOf (LVar lvar))
					(* raise (Failure (Printf.sprintf "Logical variables always have a type, in particular: %s." lvar))) *)
			| ALoc _ -> LLit (Type ObjectType)
			| PVar _ -> raise (Failure "This should never happen: program variable in normalised expression")
			| LBinOp (_, _, _)
			| LUnOp (_, _) -> LTypeOf (nle1)
			| LTypeOf _ -> LLit (Type TypeType)
			| LEList _ -> LLit (Type ListType)
			| LLstNth (list, index) ->
				(match list, index with
					| LLit (LList list), LLit (Num n) when (Utils.is_int n) ->
						let lit_n = (try List.nth list (int_of_float n) with _ ->
							raise (Failure "List index out of bounds")) in
						LLit (Type (evaluate_type_of lit_n))
					| LLit (LList list), LLit (Num n) -> raise (Failure "Non-integer list index")
					| LEList list, LLit (Num n) when (Utils.is_int n) ->
						let le_n = (try List.nth list (int_of_float n) with _ ->
							raise (Failure "List index out of bounds")) in
						f (LTypeOf le_n)
					| LEList list, LLit (Num n) -> raise (Failure "Non-integer list index")
					| _, _ -> LTypeOf (nle1))
			| LStrNth (str, index) ->
				(match str, index with
					| LLit (String s), LLit (Num n) when (Utils.is_int n) ->
						let _ = (try (String.get s (int_of_float n)) with _ ->
							raise (Failure "String index out of bounds")) in
						LLit (Type StringType)
					| LLit (String s), LLit (Num n) -> raise (Failure "Non-integer string index")
					| _, _ -> LTypeOf (nle1)))

	| LEList le_list ->
		let n_le_list = List.map (fun le -> f le) le_list in
		let all_literals, lit_list =
			List.fold_left
				(fun (ac, list) le ->
					match le with
					| LLit lit -> (ac, (list @ [ lit ]))
					| _ -> (false, list))
				(true, [])
				n_le_list in
		if (all_literals)
		then LLit (LList lit_list)
		else LEList n_le_list

	| LLstNth (le1, le2) ->
		let nle1 = f le1 in
		let nle2 = f le2 in
		(match nle1, nle2 with
			| LLit (LList list), LLit (Num n) when (Utils.is_int n) -> 
					(try LLit (List.nth list (int_of_float n)) with _ ->
						raise (Failure "List index out of bounds"))
			| LLit (LList list), LLit (Num n) -> raise (Failure "Non-integer list index")
			| LEList list, LLit (Num n) when (Utils.is_int n) -> 
					let le = (try (List.nth list (int_of_float n)) with _ ->
						raise (Failure "List index out of bounds")) in
					f le
			| LEList list, LLit (Num n) -> raise (Failure "Non-integer list index")
			| _, _ -> LLstNth (nle1, nle2))

	| LStrNth (le1, le2) ->
		let nle1 = f le1 in
		let nle2 = f le2 in
		(match nle1, nle2 with
			| LLit (String s), LLit (Num n) ->
				(try LLit (String (String.make 1 (String.get s (int_of_float n))))
				with _ -> raise (Failure "String index out of bounds"))
			| _, _ -> LStrNth (nle1, nle2)) in
		let end_time = Sys.time () in
		JSIL_Syntax.update_statistics "normalise_lexpr" (end_time -. start_time);
		print_debug_petar (Printf.sprintf "normalise_lexpr: %f : %s -> %s" 
			(end_time -. start_time) (JSIL_Print.string_of_logic_expression le false) 
			(JSIL_Print.string_of_logic_expression result false));
		result)
	with
	| Failure msg -> let end_time = Sys.time () in
		JSIL_Syntax.update_statistics "normalise_lexpr" (end_time -. start_time);
		print_debug_petar (Printf.sprintf "normalise_lexpr: %f : %s -> Failure" 
			(end_time -. start_time) (JSIL_Print.string_of_logic_expression le false));
		raise (Failure msg)

let rec normalise_pure_assertion store gamma subst assertion =
	let fa = normalise_pure_assertion store gamma subst in
	let fe = normalise_lexpr store gamma subst in
	let start_time = Sys.time() in
	try (let result = (match assertion with
	| LEq (le1, le2) -> LEq((fe le1), (fe le2))
	| LLess (le1, le2) -> LLess((fe le1), (fe le2))
	| LLessEq (le1, le2) -> LLessEq((fe le1), (fe le2))
	| LNot (LEq (le1, le2)) -> LNot (LEq((fe le1), (fe le2)))
	| LNot (LLessEq (le1, le2)) -> LNot (LLessEq((fe le1), (fe le2)))
	| LNot (LLess (le1, le2)) -> LNot (LLess((fe le1), (fe le2)))
	| LAnd (a1, a2) -> LAnd ((fa a1), (fa a2))
	| LOr (a1, a2) -> LOr ((fa a1), (fa a2))
	| LFalse -> LFalse
	| LTrue -> LTrue

	| _ ->
			let msg = Printf.sprintf "normalise_pure_assertion can only process pure assertions: %s" (JSIL_Print.string_of_logic_assertion assertion false) in
			raise (Failure msg)) in
	let end_time = Sys.time () in
	JSIL_Syntax.update_statistics "normalise_pure_assertion" (end_time -. start_time);
	print_debug (Printf.sprintf "normalise_pure_assertion: %f : %s -> %s" 
			(end_time -. start_time) (JSIL_Print.string_of_logic_assertion assertion false) 
			(JSIL_Print.string_of_logic_assertion result false));
		result)
	with
	| Failure msg -> let end_time = Sys.time () in
		JSIL_Syntax.update_statistics "normalise_pure_assertion" (end_time -. start_time);
		print_debug_petar (Printf.sprintf "normalise_pure_assertion: %f : %s -> Failure" 
			(end_time -. start_time) (JSIL_Print.string_of_logic_assertion assertion false));
		raise (Failure msg)

	

let new_abs_loc_name var = abs_loc_prefix ^ var

let unknown_name = "_lvar_unknown_"
let counter = ref 0
let new_unknown_lvar =
	(fun () ->
		counter := (!counter) + 1;
		unknown_name ^ (string_of_int !counter))


let new_lvar_name var = lvar_prefix ^ var

let rec init_symb_store_alocs store gamma subst ass : unit =
	let f = init_symb_store_alocs store gamma subst in
	match ass with
	| LStar (a_left, a_right) ->
			f a_left; f a_right

	| LPointsTo (PVar var, _, _)
	| LEmptyFields (PVar var, _) ->
			if (not (Hashtbl.mem store var))
			then
				(let aloc = new_abs_loc_name var in
					Hashtbl.add store var (ALoc aloc);
					Hashtbl.add subst var (ALoc aloc);
					Hashtbl.replace gamma var ObjectType)

	| LPointsTo (LVar var, _, _)
	| LEmptyFields (LVar var, _) ->
			if (not (Hashtbl.mem subst var))
			then
				(let aloc = new_abs_loc_name var in
					Hashtbl.add subst var (ALoc aloc))
					(* Hashtbl.remove gamma var) *)

	| LPointsTo (ALoc _, _, _) -> ()
			(* raise (Failure "Unsupported assertion during normalization") *)

	| _ -> ()



let init_pure_assignments a store gamma subst =

	let pure_assignments = Hashtbl.create 31 in
	let non_store_pure_assertions = Stack.create () in

	(**
	* After putting the variables that have assignents of the kind:
	* x = E (where E is a logical expression) in the store,
	* we have to normalise the remaining pure assertions
	*)
	let normalise_pure_assertions () =
		let stack_size = Stack.length non_store_pure_assertions in
		let non_store_pure_assertions_array = DynArray.make (stack_size *5) in
		let cur_index = ref 0 in

		while (not (Stack.is_empty non_store_pure_assertions)) do
			let pure_assertion = Stack.pop non_store_pure_assertions in
			let normalised_pure_assertion = normalise_pure_assertion store gamma subst pure_assertion in
			DynArray.add non_store_pure_assertions_array normalised_pure_assertion;
			cur_index := (!cur_index) + 1
		done;

		let non_store_pure_assertions_array = Simplifications.aggressively_simplify_pfs non_store_pure_assertions_array gamma false in
		non_store_pure_assertions_array in

	(**
	* Given an assertion a, this function returns the list of pure assignments in a.
	* assignments of the form: x = E or E = x for a logical expression E and a variable x
	*)
	let rec get_pure_assignments_iter a =
		(match a with
			| LStar (a_l, a_r) ->
					get_pure_assignments_iter a_l;
					get_pure_assignments_iter a_r

			| LEq (PVar x, le)
			| LEq (le, PVar x) ->
					if ((not (Hashtbl.mem pure_assignments x)) && (not (Hashtbl.mem store x)))
					then Hashtbl.add pure_assignments x le
					else Stack.push (LEq (PVar x, le)) non_store_pure_assertions

			| LEq (_, _) -> Stack.push a non_store_pure_assertions

			| LNot _ -> Stack.push a non_store_pure_assertions
			| LLessEq (_, _) -> Stack.push a non_store_pure_assertions
			| LLess (_, _) -> Stack.push a non_store_pure_assertions

			| LOr (_, _) -> Stack.push a non_store_pure_assertions
			| LAnd (_, _) -> Stack.push a non_store_pure_assertions

			| _ -> ()) in

	(**
	* all program variables not in the store need to be added there
	*)
	let fill_store p_vars =
		SS.iter
			(fun var ->
						if (not (Hashtbl.mem store var))
						then
							let new_l_var = new_lvar_name var in
							Hashtbl.add store var (LVar new_l_var);
							Hashtbl.add subst var (LVar new_l_var);
							(try
								let var_type = Hashtbl.find gamma var in
								Hashtbl.add gamma new_l_var var_type
							with _ -> ()))
			p_vars	in

	(**
	* dependency graphs between variable definitions
	*)
	let vars_succ p_vars p_vars_tbl =
		let len = SS.cardinal p_vars in
		let succs = Array.make len [] in
		
		List.iteri (fun u cur_var ->
			let cur_le = Hashtbl.find pure_assignments cur_var in
			let cur_var_deps = get_expr_vars true cur_le in
			SS.iter (fun v ->
				(try
					let v_num = Hashtbl.find p_vars_tbl v in
					succs.(u) <- v_num :: succs.(u)
					with _ -> ())) cur_var_deps) (SS.elements p_vars);
					
		succs in

	(**
	* normalization of variable definitions
	*)
	let normalise_pure_assignments (succs : int list array) (p_vars : SS.t) (p_vars_tbl : (string, int) Hashtbl.t) =
		let p_vars = Array.of_list (SS.elements p_vars) in
		let len = Array.length p_vars in
		let visited_tbl = Array.make len false in

		let is_searchable u =
			List.fold_left
				(fun ac v -> ac && (not visited_tbl.(v)))
				true
				succs.(u) in

		(** a pure assignment that cannot be lifted to the abstract store
		has to remain in the pure formulae *)
		let remove_assignment var =
			(try
				let new_l_var = Hashtbl.find subst var in
				let le = Hashtbl.find pure_assignments var in
				Stack.push (LEq (new_l_var, le)) non_store_pure_assertions;
				Hashtbl.remove pure_assignments var
			with _ ->
					let msg = Printf.sprintf "Should not be here: remove_assignment. Var: %s." var in
					raise (Failure msg)) in

		(** lifting an assignment to the abstract store *)
		let rewrite_assignment var =
			let le = try Some (Hashtbl.find pure_assignments var) with _ -> None in
			(match le with
				| None ->
						let msg = Printf.sprintf "Should not be here: rewrite_assignment. Var: %s\n" var in
						raise (Failure msg)
				| Some le ->
						let normalised_le = normalise_lexpr store gamma subst le in
						Hashtbl.remove subst var;
						Hashtbl.remove pure_assignments var;
						Hashtbl.replace store var normalised_le) in

		let rec search (u : int) =
			let u_var = p_vars.(u) in
			visited_tbl.(u) <- true;
			match (is_searchable u) with
			| false -> remove_assignment u_var
			| true ->
					List.iter
						(fun v ->
									if (visited_tbl.(v))
									then ()
									else search v)
						succs.(u);
					rewrite_assignment u_var in

		for i = 0 to (len - 1) do
			if (not (visited_tbl.(i)))
			then search i
			else ()
		done in

	(* get the pure assignments and store them in the hashtbl                *)
	(* pure_assignments                                                      *)
	get_pure_assignments_iter a;
	let p_vars = Hashtbl.fold
		(fun var le ac -> SS.add var ac)
		pure_assignments SS.empty in
	let p_vars_tbl = get_vars_tbl p_vars in
	let succs = vars_succ p_vars p_vars_tbl in
	normalise_pure_assignments succs p_vars p_vars_tbl;
	fill_store (get_assertion_vars true a);
	normalise_pure_assertions ()

let rec compute_symb_heap (heap : symbolic_heap) (store : symbolic_store) p_formulae gamma subst a =
	let f = compute_symb_heap heap store p_formulae gamma subst in
	let fe = normalise_lexpr store gamma subst in

	let simplify_element_of_cell_assertion ele =
		(match ele with
			| LLit _
			| LVar _
			| ALoc _
			| LNone
			| LUnknown -> ele
			| _ ->
					let lvar = fresh_lvar () in
					(* I need to add the type of the new logical variable to the gamma *)
					DynArray.add p_formulae (LEq ((LVar lvar), ele));
					let te, _, _ = JSIL_Logic_Utils.type_lexpr gamma ele in
					update_gamma gamma lvar te;
					LVar lvar) in

	match a with
	| LStar (a1, a2) -> f a1; f a2

	| LPointsTo (LVar var, le2, le3)
	| LPointsTo (PVar var, le2, le3) ->
			let aloc = (try
					(match Hashtbl.find subst var with
						| ALoc aloc -> aloc
						| _ -> raise (Failure (Printf.sprintf "Not an ALoc in subst: %s" (JSIL_Print.string_of_logic_expression (Hashtbl.find subst var) false))))
				with _ -> raise (Failure (Printf.sprintf "Variable %s not found in subst table!" var))) in
			let nle2 = simplify_element_of_cell_assertion (fe le2) in
			let nle3 = simplify_element_of_cell_assertion (fe le3) in
			let field_val_pairs, default_val = (try LHeap.find heap aloc with _ -> ([], LUnknown)) in
			LHeap.replace heap aloc (((nle2, nle3) :: field_val_pairs), default_val)

	| LPointsTo (LLit (Loc loc), le2, le3) ->
			let nle2 = simplify_element_of_cell_assertion (fe le2) in
			let nle3 = simplify_element_of_cell_assertion (fe le3) in
			let field_val_pairs, default_val = (try LHeap.find heap loc with _ -> ([], LUnknown)) in
			LHeap.replace heap loc (((nle2, nle3) :: field_val_pairs), default_val)

	| LPointsTo (ALoc loc, le2, le3) ->
			let nle2 = simplify_element_of_cell_assertion (fe le2) in
			let nle3 = simplify_element_of_cell_assertion (fe le3) in
			let field_val_pairs, default_val = (try LHeap.find heap loc with _ -> ([], LUnknown)) in
			LHeap.replace heap loc (((nle2, nle3) :: field_val_pairs), default_val)
	
	| LPointsTo (_, _, _) -> 
			raise (Failure "Illegal PointsTo Assertion")

	| _ -> ()

let rec init_gamma gamma a =
	let f = init_gamma gamma in
	match a with
	| LTypes type_list ->
			List.iter
				(fun (v, t) ->
							match v with
							| LLit lit ->
									if ((evaluate_type_of lit) = t)
									then ()
									else
										(let msg = Printf.sprintf "Only vars or lvars in the typing environment, for the love of God. PUTTING: %s with type %s"
													(JSIL_Print.string_of_logic_expression v false)
													(JSIL_Print.string_of_type t) in
											raise (Failure msg))

							| LVar v -> Hashtbl.replace gamma v t
							| PVar v -> Hashtbl.replace gamma v t
							(* let new_v, new_v_name = (match t with | ObjectType -> let new_v_name =  *)
							(* fresh_aloc () in ALoc (new_v_name), new_v_name | _ -> let new_v_name =  *)
							(* fresh_lvar () in LVar (new_v_name), new_v_name) in Hashtbl.replace      *)
							(* store v new_v; Hashtbl.replace subst v new_v; Hashtbl.replace gamma v   *)
							(* t; Hashtbl.replace gamma new_v_name t                                   *)
							| LNone -> ()
							| _ ->
									let v_type, _, _ = JSIL_Logic_Utils.type_lexpr gamma v in
									(match v_type with
										| Some v_type ->
												(if (v_type = t)
													then ()
													else (
														let msg = Printf.sprintf "Only vars or lvars in the typing environment. PUTTING: %s with type %s when its type is %s"
																(JSIL_Print.string_of_logic_expression v false)
																(JSIL_Print.string_of_type t)
																(JSIL_Print.string_of_type v_type) in
														raise (Failure msg)))
										| None ->
												let new_gamma = JSIL_Logic_Utils.reverse_type_lexpr gamma v t in
												(match new_gamma with
													| None ->
															let msg = Printf.sprintf "Only vars or lvars in the typing environment. PUTTING: %s with type %s when it CANNOT be typed or reverse-typed"
																	(JSIL_Print.string_of_logic_expression v false)
																	(JSIL_Print.string_of_type t) in
															raise (Failure msg)
													| Some new_gamma ->
															extend_gamma gamma new_gamma)))
				type_list
	| LStar	(al, ar) -> f al; f ar
	| _ -> ()


let init_preds a store gamma subst =
	let preds = DynArray.make 11 in

	let make_normalised_pred_assertion name les =
		let new_les, new_assertions =
			List.fold_left
				(fun (new_les, new_equalities) le ->
					match le with
					| LNone	| LVar _ | LLit _ | ALoc _ -> ((le :: new_les), new_equalities)
					| PVar x ->
						print_debug_petar (Printf.sprintf "Inside init_preds (%s)\n" (JSIL_Print.string_of_logic_assertion a false));
						print_debug_petar (Printf.sprintf "Currrent Store: %s\n" (Symbolic_State_Print.string_of_shallow_symb_store store false));
						print_debug_petar (Printf.sprintf "Current Substitution: %s\n" (Symbolic_State_Print.string_of_substitution subst));
						print_debug_petar (Printf.sprintf "Program Variable %s in logical expression that was supposed to be normalised!!!\n" x);
						raise (Failure "")
					| _ ->
						let x = fresh_lvar () in
						((LVar x) :: new_les), ((LEq ((LVar x), le)) :: new_equalities))
				([], [])
				les in
		let new_les = List.rev new_les in
		(name, new_les), new_assertions in

	let rec init_preds_aux preds a =
		let f = init_preds_aux preds in
		let fe = normalise_lexpr store gamma subst in
		(match a with
			| LStar (a1, a2) ->
				let new_assertions1 = f a1 in
				let new_assertions2 = f a2 in
				new_assertions1 @ new_assertions2
			| LPred (name, les) ->
					let n_les =	List.map fe les in
					let normalised_pred_assertion, new_assertions = make_normalised_pred_assertion name n_les in
					DynArray.add preds normalised_pred_assertion;
					new_assertions
			| _ -> []) in
	let new_assertions = init_preds_aux preds a in
	let dna = DynArray.of_list new_assertions in
	Simplifications.sanitise_pfs store gamma dna;
	preds, (DynArray.to_list dna)

let fill_store_with_gamma store gamma subst =
	Hashtbl.iter
		(fun var t ->
					if ((is_pvar_name var) && (not (Hashtbl.mem store var)))
					then
						let new_l_var = new_lvar_name var in
						Hashtbl.add gamma new_l_var t;
						Hashtbl.add store var (LVar new_l_var);
						Hashtbl.add subst var (LVar new_l_var))
		gamma

let extend_typing_env_using_assertion_info a_list gamma =
	let rec loop a_list =
		match a_list with
		| [] -> ()
		| (LEq (LVar x, le)) :: rest_a_list
		| (LEq (le, LVar x)) :: rest_a_list
		| (LEq (PVar x, le)) :: rest_a_list
		| (LEq (le, PVar x)) :: rest_a_list ->
			let x_type = gamma_get_type gamma x in
			(match x_type with
			| None ->
				let le_type, _, _ = JSIL_Logic_Utils.type_lexpr gamma le in
				weak_update_gamma gamma x le_type
			| Some _ -> ());
			loop rest_a_list
		| _ :: rest_a_list -> loop rest_a_list in
	loop a_list

let process_empty_fields heap store p_formulae gamma subst a =

	let rec gather_empty_fields a =
		let f = gather_empty_fields in
		match a with
		| LAnd (_, _) | LOr (_, _) | LNot _ | LTrue | LFalse | LEq (_, _)
			| LLess (_, _) | LLessEq (_, _) | LStrLess (_, _) | LEmp
			| LTypes (_) | LPred (_, _) | LPointsTo (_, _, _) -> []
		| LStar (a1, a2) -> (f a1) @ (f a2)
		| LEmptyFields (le, fields) ->
				let le' = normalise_lexpr store gamma subst le in
				[ (le', fields) ] in

	let rec check_in_fields (le_field : jsil_logic_expr) (fields : jsil_logic_expr list) (traversed_fields : jsil_logic_expr list) : (jsil_logic_expr * (jsil_logic_expr list)) option =
		match fields with
		| [] -> None
		| field :: rest_fields ->
			let a = LEq (le_field, field) in
			if (Pure_Entailment.old_check_entailment SS.empty p_formulae [ a ] gamma)
				then Some (field, traversed_fields @ rest_fields)
				else 
					(if (Pure_Entailment.old_check_entailment SS.empty p_formulae [ LNot a ] gamma)
						then check_in_fields le_field rest_fields (field :: traversed_fields) 
						else raise (Failure "empty fields assertion cannot be normalised")) in 

	let rec close_fields (fields : jsil_logic_expr list) (fv_list : (jsil_logic_expr * jsil_logic_expr) list) (found_fields : jsil_logic_expr list) =
		match fv_list with
		| [] -> fields, found_fields
		| (le_field, le_val) :: rest_fv_list ->
			let ret : (jsil_logic_expr * (jsil_logic_expr list)) option = check_in_fields le_field fields [] in
			(match ret with
			| None ->
				if (le_val <> LNone)
					then raise 
						(Failure (
							Printf.sprintf "empty_fields assertion incompatible with cell assertion. Field %s is not in the none-fields: {{ %s }}" 
								(JSIL_Print.string_of_logic_expression le_field false)
								(String.concat ", "
									(List.map (fun le -> JSIL_Print.string_of_logic_expression le false) fields))))
					else close_fields fields rest_fv_list found_fields
			| Some (found_field, rest_fields) ->
				close_fields rest_fields rest_fv_list (found_field :: found_fields)) in

	let rec make_fv_list_missing_fields missing_fields fv_list =
		let new_lvar = new_unknown_lvar () in
		match missing_fields with
		| [] -> fv_list
		| field :: rest -> make_fv_list_missing_fields rest ((field, LVar new_lvar) :: fv_list) in

	let close_object le_loc (non_none_fields : jsil_logic_expr list) =
		print_debug_petar (Printf.sprintf "Location: %s" (JSIL_Print.string_of_logic_expression le_loc false));
		let le_loc_name =
			match le_loc with
			| LLit (Loc loc_name)
			| ALoc loc_name -> loc_name
			| PVar x
			| LVar x ->
				let x_loc = try Hashtbl.find subst x with _ ->
					print_debug_petar "Variable not in subst."; raise (Failure "Illegal Emptyfields!!!") in
				(match x_loc with
				| ALoc loc
				| LLit (Loc loc) -> loc
				| _ -> print_debug_petar "Variable strange after subst."; raise (Failure "Illegal Emptyfields!!!"))
			| _ -> raise (Failure "Illegal Emptyfields!!!") in

		let ret =
		    print_debug_petar (Printf.sprintf "le_loc: %s\nNasty fields:\n" (JSIL_Print.string_of_logic_expression le_loc false));
			List.iter (fun s -> print_debug_petar (Printf.sprintf "\t%s\n" (JSIL_Print.string_of_logic_expression s false))) non_none_fields;
			print_debug_petar (Printf.sprintf "Heap: %s\n" (Symbolic_State_Print.string_of_shallow_symb_heap heap false));
			LHeap.fold (fun cur_loc (cur_fv_list, cur_def) ac ->
				match ac with
				| Some _ -> ac
				| None ->
				 	if (le_loc_name = cur_loc) then (
						let missing_fields, _ = close_fields non_none_fields cur_fv_list [] in
						let new_cur_fv_list = make_fv_list_missing_fields missing_fields cur_fv_list in
						Some (cur_loc, new_cur_fv_list)
					) else None)
			heap
			None in
		match ret with
		| Some (loc, new_fv_list) -> LHeap.replace heap loc (new_fv_list, LNone)
		| None -> LHeap.replace heap le_loc_name (make_fv_list_missing_fields non_none_fields [], LNone) in

	let fields_to_close = gather_empty_fields a in
	List.iter (fun (le, non_none_fields) -> close_object le non_none_fields) fields_to_close



let normalise_assertion a : symbolic_state * substitution =
	
	print_debug_petar (Printf.sprintf "Normalising assertion:\n\t%s" (JSIL_Print.string_of_logic_assertion a false));
	
	let heap = LHeap.create 101 in
	let store = Hashtbl.create 101 in
	let gamma = Hashtbl.create 101 in
	let subst = Hashtbl.create 101 in

	init_gamma gamma a;
	init_symb_store_alocs store gamma subst a;

	let p_formulae = init_pure_assignments a store gamma subst in

	 (match (DynArray.to_list p_formulae) with
	 | [ LFalse ] -> (LHeap.create 1, Hashtbl.create 1, DynArray.of_list [ LFalse ], Hashtbl.create 1, DynArray.create()), Hashtbl.create 1
	 | _ ->
		fill_store_with_gamma store gamma subst;
		extend_typing_env_using_assertion_info ((pfs_to_list p_formulae) @ (pf_of_store2 store)) gamma;
		compute_symb_heap heap store p_formulae gamma subst a;
		let preds, new_assertions = init_preds a store gamma subst in
		extend_typing_env_using_assertion_info new_assertions gamma;
		merge_pfs p_formulae (DynArray.of_list new_assertions);
		process_empty_fields heap store (pfs_to_list p_formulae) gamma subst a;
		(heap, store, p_formulae, gamma, preds), subst)


let connecting_logical_vars_with_abstract_locations_in_post pre_vars subst new_subst = 
	SS.fold (fun  x ac ->
		if ((is_lvar_name x) && (Hashtbl.mem new_subst x) && (not (Hashtbl.mem subst x)))
			then (LEq (LVar x, Hashtbl.find new_subst x)) :: ac 
			else ac)
			pre_vars 
			[]


let normalise_precondition a =
	let lvars = get_assertion_vars false a in
	let symb_state, subst = normalise_assertion a in
	let new_subst = filter_substitution subst lvars in
	symb_state, (lvars, new_subst)

let normalise_postcondition a subst (lvars : SS.t) pre_gamma : symbolic_state * SS.t =
	let a = assertion_substitution a subst true in
	let a_vars : SS.t = get_assertion_vars false a in
	let post_existentials : SS.t = filter_vars a_vars lvars in

	let extra_gamma = filter_gamma pre_gamma lvars in
	let a_vars_str = List.fold_left (fun ac var -> (ac ^ var ^ ", ")) "" (SS.elements post_existentials) in
	let lvars_str = String.concat ", " (SS.elements lvars) in

	(**
	print_debug_petar (Printf.sprintf "Post Existentially Quantified Vars: %s" a_vars_str);
	print_debug_petar (Printf.sprintf "Post spec vars: %s" lvars_str);
	let symb_state, _ = normalise_assertion a in
	*)
	
	print_debug (Printf.sprintf "Post Existentially Quantified Vars: %s" a_vars_str);
	print_debug (Printf.sprintf "Post spec vars: %s" lvars_str);
	let symb_state, new_subst = normalise_assertion a in
	print_debug (Printf.sprintf "Subst: %s" (Symbolic_State_Print.string_of_substitution subst));
	print_debug (Printf.sprintf "New subst: %s" (Symbolic_State_Print.string_of_substitution new_subst));
	let more_pfs = connecting_logical_vars_with_abstract_locations_in_post lvars subst new_subst in 
	if (List.length more_pfs > 0) then (
		print_debug "Connecting:\n";
		List.iter (fun a -> print_debug (Printf.sprintf "\t%s" (JSIL_Print.string_of_logic_assertion a false))) more_pfs);
	extend_symb_state_with_pfs symb_state (DynArray.of_list more_pfs); 
	
	let gamma_post = (get_gamma symb_state) in
	merge_gammas gamma_post extra_gamma;
	symb_state, post_existentials


let pre_normalise_invariants_proc preds body = 
	let f_pre_normalize a_list = List.concat (List.map pre_normalize_assertion a_list) in
	let len = Array.length body in
	for i = 0 to (len - 1) do 
		let metadata, cmd = body.(i) in 
		match metadata.invariant with 
		| None -> () 
		| Some a -> (
				let unfolded_a = f_pre_normalize (Logic_Predicates.auto_unfold preds a) in
				match unfolded_a with 
				| [] -> raise (Failure "invariant unfolds to ZERO assertions")
				| [ a ] -> body.(i) <- { metadata with invariant = Some a }, cmd 
				| _ -> raise (Failure "invariant unfolds to MORE THAN ONE assertion")
			)
	done
	

let pre_normalise_invariants_prog preds prog = 
	Hashtbl.iter (fun proc_name proc -> pre_normalise_invariants_proc preds proc.proc_body) prog
			

let normalise_single_spec preds spec =
	print_time_debug"  normalise_single_spec:";

	print_debug (Printf.sprintf "Precondition  : %s" (JSIL_Print.string_of_logic_assertion spec.pre false));
	print_debug (Printf.sprintf "Postcondition : %s" (JSIL_Print.string_of_logic_assertion spec.post false));

	print_debug (Printf.sprintf "NSS: Entry");

	let f_pre_normalize a_list = List.concat (List.map pre_normalize_assertion a_list) in
	let f_print assertions =
		List.fold_left (fun ac s -> if (ac = "\n") then ac ^ s else (ac ^ ";\n\n" ^ s)) "\n"
			(List.map (fun a -> JSIL_Print.string_of_logic_assertion a false) assertions) in

	let unfolded_pres = f_pre_normalize (Logic_Predicates.auto_unfold preds spec.pre) in
	let unfolded_posts = f_pre_normalize (Logic_Predicates.auto_unfold preds spec.post) in

	print_debug (Printf.sprintf "NSS: Pre-normalise\n");

	print_debug (Printf.sprintf "Pres: %s" (f_print unfolded_pres));
	print_debug (Printf.sprintf "Posts: %s" (f_print unfolded_posts));

	let unfolded_spec_list =
		List.map
			(fun pre ->
						let pre_symb_state, (lvars, subst) = normalise_precondition pre in
						print_debug (Printf.sprintf "I am going to check whether the following precondition makes sense:\n%s\n"
							(Symbolic_State_Print.string_of_shallow_symb_state pre_symb_state));
						let heap_constraints = Symbolic_State_Utils.get_heap_well_formedness_constraints (get_heap pre_symb_state) in
						print_debug_petar (Printf.sprintf "heap constraints:\n%s" (List.fold_left (fun ac x -> ac ^ "\t" ^ JSIL_Print.string_of_logic_assertion x false ^ "\n") "" heap_constraints));
						let is_valid_precond = Pure_Entailment.check_satisfiability (heap_constraints @ (get_pf_list pre_symb_state)) (get_gamma pre_symb_state) in
						if (is_valid_precond)
						then begin
							print_debug (Printf.sprintf "The precondition makes sense.");
							(let posts, posts_lvars =
									List.fold_left
										(fun (ac_posts, ac_posts_lvars) post ->
											print_debug ("POST: Checking a postcondition.\n");
											print_debug_petar (Printf.sprintf "%s" (JSIL_Print.string_of_logic_assertion post false));
											print_debug_petar (Printf.sprintf "POST: Gamma from the pre: %s" (Symbolic_State_Print.string_of_gamma (get_gamma pre_symb_state)));
											let post_symb_state, post_lvars = normalise_postcondition post subst lvars (get_gamma pre_symb_state) in
											print_debug_petar (Printf.sprintf "POST: Gamma from the post: %s" (Symbolic_State_Print.string_of_gamma (get_gamma post_symb_state)));
											let heap_constraints = Symbolic_State_Utils.get_heap_well_formedness_constraints (get_heap post_symb_state) in
											print_debug_petar (Printf.sprintf "For the postcondition to make sense the following must be satisfiable:\n%s\n"
												(JSIL_Print.str_of_assertion_list (heap_constraints @ (get_pf_list post_symb_state))));
											if (Pure_Entailment.check_satisfiability (heap_constraints @ (get_pf_list post_symb_state)) (get_gamma post_symb_state))
											then ((post_symb_state :: ac_posts), (post_lvars :: ac_posts_lvars))
											else ac_posts, ac_posts_lvars)
										([], [])
										unfolded_posts in
								(if (posts = []) then print_debug (Printf.sprintf "WARNING: No valid postconditions found."));
								Some {
									n_pre = pre_symb_state;
									n_post = posts;
									n_ret_flag = spec.ret_flag;
									n_lvars = lvars;
									n_post_lvars = posts_lvars;
									n_subst = subst
								})
						end else begin
							print_debug (Printf.sprintf "WARNING: The precondition does not make sense.");
							None
						end)
			unfolded_pres in
	let unfolded_spec_list =
		List.fold_left
			(fun ac elem ->
						match elem with
						| None -> ac
						| Some spec -> spec :: ac)
			[]
			unfolded_spec_list in
	unfolded_spec_list

let normalise_spec preds spec =
	let time = Sys.time () in
	print_debug (Printf.sprintf "Going to process the SPECS of %s. The time now is: %f\n" spec.spec_name time);
	let normalised_pre_post_list = List.concat (List.map (normalise_single_spec preds) spec.proc_specs) in
	let normalised_pre_post_list =
		List.map (fun (x : jsil_n_single_spec) ->
			let pre = Simplifications.simplify false x.n_pre in
			let post = List.map (fun y -> Simplifications.simplify false y) x.n_post in
			{ x with n_pre = pre; n_post = post }
		) normalised_pre_post_list in
	{
		n_spec_name = spec.spec_name;
		n_spec_params = spec.spec_params;
		n_proc_specs = normalised_pre_post_list
	}

let build_spec_tbl preds prog onlyspecs =
	let spec_tbl = Hashtbl.create 511 in
	Hashtbl.iter
		(fun proc_name proc ->
					match proc.spec with
					| None -> ()
					| Some spec ->
							let msg = Printf.sprintf "\n*************************\n* Normalising the spec: *\n*************************\n\n%s" (Symbolic_State_Print.string_of_jsil_spec spec) in
							print_debug (msg);
							let n_spec = normalise_spec preds spec in
							Hashtbl.replace spec_tbl n_spec.n_spec_name n_spec)
		prog;
	Hashtbl.iter
		(fun spec_name spec ->
			let msg = Printf.sprintf "\n*************************\n* Normalising the spec: *\n*************************\n\n%s" (Symbolic_State_Print.string_of_jsil_spec spec) in
			print_debug (msg);
			let n_spec = normalise_spec preds spec in
			Hashtbl.replace spec_tbl n_spec.n_spec_name n_spec)
		onlyspecs;
	print_debug (Printf.sprintf "-----------------------------\n-----------------------------\nSpec Table:\n%s" (Symbolic_State_Print.string_of_n_spec_table spec_tbl));
	spec_tbl



let normalise_predicate_definitions pred_defs : (string, Symbolic_State.n_jsil_logic_predicate) Hashtbl.t =
	print_debug "Normalising predicate definitions.\n";
	let n_pred_defs = Hashtbl.create 31 in
	Hashtbl.iter
		(fun pred_name pred ->
					let n_definitions =
						List.map
							(fun a ->
										let pre_normalised_as = pre_normalize_assertion a in
										let normalised_as = List.map
											(fun a ->
														let symb_state, _ = normalise_assertion a in
														symb_state)
											pre_normalised_as in
										let normalised_as = List.filter
											(fun symb_state ->
												let heap_constraints = Symbolic_State_Utils.get_heap_well_formedness_constraints (get_heap symb_state) in
												print_debug_petar (Printf.sprintf "Symbolic state to check: %s\n%s\n" pred_name (Symbolic_State_Print.string_of_shallow_symb_state symb_state));
												((check_store (get_store symb_state) (get_gamma symb_state)) && (Pure_Entailment.check_satisfiability (heap_constraints @ (get_pf_list symb_state)) (get_gamma symb_state))))
											normalised_as in
										(if ((List.length normalised_as) = 0)
											then print_debug (Printf.sprintf "WARNING: One predicate definition does not make sense: %s\n" pred_name));
										normalised_as)
							pred.definitions in
					let n_definitions = List.rev (List.concat n_definitions) in
					let n_pred = {
						n_pred_name = pred.name;
						n_pred_num_params = pred.num_params;
						n_pred_params = pred.params;
						n_pred_definitions = n_definitions;
						n_pred_is_rec = pred.is_recursive
					} in
					Hashtbl.replace n_pred_defs pred_name n_pred)
		pred_defs;
	n_pred_defs
