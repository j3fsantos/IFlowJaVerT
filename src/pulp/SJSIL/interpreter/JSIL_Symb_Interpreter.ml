open Entailment_Engine
open JSIL_Syntax
open JSIL_Memory_Model
open JSIL_Logic_Utils

let verbose = ref true

let proto_f = "@proto"



let pf_substitution pf_r subst partial =
	let new_pf = DynArray.create () in
	let len = (DynArray.length pf_r) - 1 in
	for i=0 to len do
		let a = DynArray.get pf_r i in
		let s_a = assertion_substitution a subst partial in
		DynArray.add new_pf s_a
	done;
	new_pf


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
						if (partial) then
							if (is_abs_loc_name loc) then (ALoc loc) else (LLit (Loc loc))
						else
							begin
								let new_aloc = ALoc (fresh_aloc ()) in
								extend_subst subst loc new_aloc;
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
			let s_def = lexpr_substitution def subst partial in
			LHeap.add new_heap s_loc (s_fv_list, s_def))
		heap;
	new_heap


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


let symb_state_substitution symb_state subst partial =
	let heap, store, pf, gamma, preds = symb_state in
	let s_heap = heap_substitution heap subst partial in
	let s_store = JSIL_Logic_Normalise.store_substitution store gamma subst partial in
	let s_pf = pf_substitution pf subst partial  in
	(*Printf.printf "partial: %b. the gamma as it is now: %s.\n" partial (JSIL_Memory_Print.string_of_gamma gamma); *)
	let s_gamma = gamma_substitution gamma subst partial in
	let s_preds = preds_substitution preds subst partial in
	(s_heap, s_store, s_pf, s_gamma, s_preds)



let rec symb_evaluate_expr (expr : jsil_expr) store gamma pure_formulae =
	match expr with
	| Literal lit -> LLit lit

	| Var var ->
		(try Hashtbl.find store var
		with _ ->
			extend_abs_store var store gamma)

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

	| VRef (e1, e2) ->
		let nle1 = symb_evaluate_expr e1 store gamma pure_formulae in
		let nle2 = symb_evaluate_expr e2 store gamma pure_formulae in
		(match nle1, nle2 with
		| LLit l, LLit (String field) -> LLit (LVRef (l, field))
		| _, _ -> LEVRef (nle1, nle2))

	| ORef (e1, e2) ->
		let nle1 = symb_evaluate_expr e1 store gamma pure_formulae in
		let nle2 = symb_evaluate_expr e2 store gamma pure_formulae in
		(match nle1, nle2 with
		| LLit l, LLit (String field) -> LLit (LORef (l, field))
		| _, _ -> LEORef (nle1, nle2))

	| Base	(e) ->
		let nle = symb_evaluate_expr e store gamma pure_formulae in
		(match nle with
		| LLit (LVRef (l, _))
		| LLit (LORef (l, _)) -> LLit l
		| LEVRef (eb, _)
		| LEORef (eb, _) -> eb
		| _ -> LBase (nle))

	| Field	(e) ->
		let nle = symb_evaluate_expr e store gamma pure_formulae in
		(match nle with
		| LLit (LVRef (_, f))
		| LLit (LORef (_, f)) -> LLit (String f)
		| LEVRef (_, fe)
		| LEORef (_, fe) -> fe
		| _ -> LField (nle))

	| TypeOf (e) ->
		let nle = symb_evaluate_expr e store gamma pure_formulae in
		(match nle with
		| LLit llit -> LLit (Type (JSIL_Interpreter.evaluate_type_of llit))
		| LNone -> raise (Failure "Illegal Logic Expression: TypeOf of None")
		| PVar _ -> raise (Failure "This should never happen: program variable in normalized expression")
		| LVar var ->
			(try
				let var_type = Hashtbl.find gamma var in
				LLit (Type var_type)
			with _ -> LTypeOf (nle))
		| ALoc _ -> LLit (Type ObjectType)
		| LBinOp (_, _, _)
		| LUnOp (_, _) -> LTypeOf (nle)
		| LEVRef (_, _) -> LLit (Type VariableReferenceType)
		| LEORef (_, _) -> LLit (Type ObjectReferenceType)
		(* this is not correct *)
		| LBase _ -> LLit (Type ObjectType)
		| LField _ -> LLit (Type StringType)
		| LTypeOf _ -> LLit (Type TypeType))

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

		(* | str, index ->
			let type_str, _ = JSIL_Logic_Utils.normalised_is_typable gamma str in
			let type_index, _ = JSIL_Logic_Utils.normalised_is_typable gamma index in
			(match type_str, type_index with
			| Some StringType, Some IntType ->
				let asrt1 = (LNot (LLess (index, LLit (Integer 0)))) in
				let asrt2 = (LLess (index, LUnOp (StrLen, str))) in
				if (Entailment_Engine.check_entailment [] (pfs_to_list pure_formulae) [ asrt1; asrt2 ] gamma)
					then begin
						let var = JSIL_Memory_Model.fresh_lvar () in
						update_gamma gamma var (Some StringType);
						LVar var
					end else LStrNth (str, index) *)
			| _, _ -> LStrNth (str, index))

	| _ -> raise (Failure "not supported yet")


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


let safe_symb_evaluate_expr (expr : jsil_expr) store gamma pure_formulae  =
	let nle = symb_evaluate_expr expr store gamma pure_formulae in
	let nle_type, is_typable = Entailment_Engine.normalised_is_typable gamma (Some pure_formulae) nle in
	if (is_typable) then
		nle, nle_type, is_typable
	else
		(match nle with
		| LLit _
		| ALoc _
		| LVar _ ->  nle, None, false
		| _ ->
			begin
				let gamma_str = JSIL_Memory_Print.string_of_gamma gamma in
				let msg = Printf.sprintf "The logical expression %s is not typable in the typing enviroment: %s" (JSIL_Print.string_of_logic_expression nle false) gamma_str in
				raise (Failure msg)
			end)

(** Turns a logical expression into an assertions.
    Returns a logical expression option and an assertion option. *)
let rec lift_logic_expr lexpr =
	(* TODO: Think of how to structure this code better *)
	let f = lift_logic_expr in
	(match lexpr with
	| LBinOp (le1, op, le2) -> lift_binop_logic_expr op le1 le2
	| LUnOp (op, le) -> lift_unop_logic_expr op le
	| LLit (Bool true) -> None, Some LTrue
	| LLit (Bool false) -> None, Some LFalse
	| _ -> Some lexpr, Some (LEq (lexpr, LLit (Bool true))))
and lift_binop_logic_expr op le1 le2 =
	let err_msg = "logical expression binop cannot be lifted to assertion" in
	let f = lift_logic_expr in
	let lexpr_to_ass_binop binop =
		(match binop with
		| Equal -> (fun le1 le2 -> LEq (le1, le2))
		| LessThan -> (fun le1 le2 -> LLess (le1, le2))
		| LessThanString -> (fun le1 le2 -> LStrLess (le1, le2))
		| LessThanEqual -> (fun le1 le2 -> LLessEq (le1, le2))
		| _ -> raise (Failure "Error: lift_binop_expr")) in
	(match op with
	| Equal
	| LessThan
	| LessThanString
	| LessThanEqual ->
		let l_op_fun = lexpr_to_ass_binop op in
		(match ((f le1), (f le2)) with
		| ((Some le1, _), (Some le2, _)) -> None, Some (l_op_fun le1 le2)
		| (_, _) -> raise (Failure (err_msg ^ " <=#")))
	| And ->
		(match ((f le1), (f le2)) with
		| ((_, Some a1), (_, Some a2)) -> None, Some (LAnd (a1, a2))
		| (_, _) -> raise (Failure err_msg))
	| Or ->
		(match ((f le1), (f le2)) with
		| ((_, Some a1), (_, Some a2)) -> None, Some (LOr (a1, a2))
		| (_, _) -> raise (Failure err_msg))
	| _ -> Some (LBinOp (le1, op, le2)), None)
and lift_unop_logic_expr op le =
	let f = lift_logic_expr in
	let err_msg = "logical expression unop cannot be lifted to assertion" in
	(match op with
	| Not ->
		(match (f le) with
		| (None, Some a) -> None, Some (LNot a)
		| (_, _) -> raise (Failure (err_msg ^ " Not")))
	| _ -> Some (LUnOp (op, le)), None)




let is_equal e1 e2 pure_formulae gamma =
  (* Printf.printf "Checking if %s is equal to %s given that: %s\n;" (JSIL_Print.string_of_logic_expression e1 false) (JSIL_Print.string_of_logic_expression e2 false) (JSIL_Memory_Print.string_of_shallow_p_formulae pure_formulae false); *)

	match e1, e2 with
	| LLit l1, LLit l2 -> l1 = l2
	| ALoc aloc1 , ALoc aloc2 -> aloc1 = aloc2
	| LNone, LNone -> true
	| LUnknown, LUnknown -> false
	| LVar l1, LVar l2 ->
		if (l1 = l2)
			then true
			else Entailment_Engine.check_entailment [] (pfs_to_list pure_formulae) [ (LEq (e1, e2)) ] gamma
	| _, _ -> Entailment_Engine.check_entailment [] (pfs_to_list pure_formulae) [ (LEq (e1, e2)) ] gamma



let isDifferent e1 e2 pure_formulae gamma =
	match e1, e2 with
	| LLit l1, LLit l2 -> (not (l1 = l2))
	| ALoc aloc1, ALoc aloc2 -> (not (aloc1 = aloc2))
	| _, _ -> Entailment_Engine.check_entailment [] (DynArray.to_list pure_formulae) [ (LNot (LEq (e1, e2))) ] gamma

(**
  find_field fv_list e p_formulae = fv_list', (e1, e2)
	   st:
		    fv_list = fv_list' U (e1, e2)
				and
				pure_formulae |=

*)
let find_field loc fv_list e p_formulae gamma =
	let rec find_field_rec fv_list traversed_fv_list i_am_sure_the_field_does_not_exist =
		match fv_list with
		| [] -> traversed_fv_list, None, i_am_sure_the_field_does_not_exist
		| (e_field, e_value) :: rest ->
			(if (is_equal e e_field p_formulae gamma)
				then traversed_fv_list @ rest, Some (e_field, e_value), false
				else
					(if (i_am_sure_the_field_does_not_exist && (isDifferent e e_field p_formulae gamma))
						then find_field_rec rest ((e_field, e_value) :: traversed_fv_list) true
						else find_field_rec rest ((e_field, e_value) :: traversed_fv_list) false)) in
	find_field_rec fv_list [] true


let update_abs_heap_default (heap : symbolic_heap) loc e =
	let fv_list, default_val = try LHeap.find heap loc with _ -> [], LUnknown in
	match default_val with
	| LUnknown -> LHeap.replace heap loc (fv_list, e)
 	| _ -> raise (Failure "the default value for the fields of a given object cannot be changed once set")


let update_abs_heap (heap : symbolic_heap) loc e_field e_val p_formulae gamma =
	(* Printf.printf "Update Abstract Heap\n"; *)
	let fv_list, default_val = try LHeap.find heap loc with _ -> [], LUnknown in
	let unchanged_fv_list, field_val_pair, i_am_sure_the_field_does_not_exist = find_field loc fv_list e_field p_formulae gamma in
	match field_val_pair, i_am_sure_the_field_does_not_exist with
	| Some _, _
	| None, true -> LHeap.replace heap loc ((e_field, e_val) :: unchanged_fv_list, default_val)
	| None, false ->
		let msg = Printf.sprintf "Cannot decide if %s exists in object %s" (JSIL_Print.string_of_logic_expression e_field false) loc in
			raise (Failure msg)


let abs_heap_find heap l e p_formulae gamma =
	let fv_list, default_val = try LHeap.find heap l with _ -> [], LUnknown in
	let _, field_val_pair, i_am_sure_the_field_does_not_exist = find_field l fv_list e p_formulae gamma in
	match field_val_pair, i_am_sure_the_field_does_not_exist with
	| Some (_, f_val), _ -> f_val
	| None, true -> default_val
	| None, false ->
		let msg = Printf.sprintf "Cannot decide if %s exists in object %s" (JSIL_Print.string_of_logic_expression e false) l in
			raise (Failure msg)

let abs_heap_check_field_existence heap l e p_formulae gamma =
	let f_val = abs_heap_find heap l e p_formulae gamma in
	match f_val with
	| LUnknown -> None
	| LNone -> Some false
	|	_ ->
		if (is_equal f_val LNone p_formulae gamma) then
			(Some false)
			else (if (isDifferent f_val LNone p_formulae gamma) then
				(Some true)
				else None)

let abs_heap_delete heap l e p_formulae gamma =
	let fv_list, default_val = try LHeap.find heap l with _ -> [], LUnknown in
	let rest_fv_pairs, del_fv_pair, _ = find_field l fv_list e p_formulae gamma in
	match del_fv_pair with
	| Some (_, _) -> LHeap.replace heap l (rest_fv_pairs, default_val)
	| None -> raise (Failure "Trying to delete an inexistent field")



let predicate_assertion_equality pred pat_pred pfs gamma spec_vars =
	let spec_vars_str = List.fold_left (fun ac v -> if (ac = "") then v else (ac ^ ", " ^ v)) "" spec_vars in
	let subst = init_substitution [] in

	let rec unify_pred_args les pat_les =
		(match les, pat_les with
		| [], [] -> Some subst
		| le :: rest_les, pat_le :: rest_pat_les ->
			(* Printf.printf "I am going to test if %s CAN BE equal to %s\n" (JSIL_Print.string_of_logic_expression le1 false) (JSIL_Print.string_of_logic_expression le2 false); *)
			(match pat_le with
			| LVar l2 when (not (List.mem l2 spec_vars)) ->
				extend_subst subst l2 le;
				unify_pred_args rest_les rest_pat_les
			| _ ->
				if (is_equal le pat_le pfs gamma)
					then unify_pred_args rest_les rest_pat_les
					else None)) in

	match pred, pat_pred with
	| (name, les), (pat_name, pat_les) ->
		if (name = pat_name) then
			unify_pred_args les pat_les
		else None
	| _, _ -> raise (Failure "predicate_assertion_equality: FATAL ERROR")



let subtract_pred pred_name args pred_set pfs gamma spec_vars =
	let pred_list = DynArray.to_list pred_set in
	let rec loop pred_list index =
		(match pred_list with
		| [] -> raise (Failure (Printf.sprintf "Predicate %s not found in the predicate set!!!" pred_name))
		| pred :: rest_pred_list ->
			(match (predicate_assertion_equality pred (pred_name, args) pfs gamma spec_vars) with
			| None -> loop rest_pred_list (index + 1)
			| Some subst -> index, subst)) in

	let index, subst = loop pred_list 0 in
	DynArray.delete pred_set index;
	subst


let unify_stores (pat_store : symbolic_store) (store : symbolic_store) (pat_subst : substitution) (subst: substitution option) (pfs : jsil_logic_assertion list) (gamma : typing_environment) : ((jsil_logic_expr * jsil_logic_expr) list) option  =
	try
	let discharges =
		Hashtbl.fold
			(fun var pat_lexpr discharges ->
				let lexpr = try Hashtbl.find store var with _ -> raise (Failure "the stores are not unifiable") in
				match pat_lexpr, lexpr with

				| LLit (Num n), LLit (Integer i)
				| LLit (Integer i), LLit (Num n) ->
					if ((n = (snd (modf n))) && (i = (int_of_float n)))
						then discharges
						else raise (Failure "the stores are not unifiable")

				| LLit pat_lit, LLit lit ->
					if (lit = pat_lit)
						then discharges
						else raise (Failure "the stores are not unifiable")

				| ALoc pat_aloc, ALoc aloc ->
					extend_subst pat_subst pat_aloc (ALoc aloc);
					discharges

				| LVar lvar, _ ->
					extend_subst pat_subst lvar lexpr;
					discharges

				| ALoc pat_aloc, LVar lvar ->
					(match subst with
					| Some subst ->
						let new_aloc = ALoc (fresh_aloc ()) in
						extend_subst subst lvar new_aloc;
						extend_subst pat_subst pat_aloc new_aloc;
						discharges
					| None -> raise (Failure "the pattern store is not normalized."))

				| LLit lit, LVar lvar ->
					(match subst with
					| Some subst ->
						extend_subst subst lvar (LLit lit);
						discharges
					| None ->
						if (Entailment_Engine.check_entailment [] pfs [ (LEq (LVar lvar, LLit lit)) ] gamma)
							then discharges
							else raise (Failure "the pattern store is not normalized."))

				| le_pat, le -> ((le_pat, le) :: discharges))
			pat_store
			[] in
	Some discharges
	with _ -> None


let unify_lexprs le_pat (le : jsil_logic_expr) p_formulae (gamma: typing_environment) (subst : (string, jsil_logic_expr) Hashtbl.t) : (bool * ((string * jsil_logic_expr) option)) =
	match le_pat with
	| LVar var
	| ALoc var ->
		(try
			let le_pat_subst = (Hashtbl.find subst var) in
			(* Printf.printf "le_pat_subst: %s. le: %s\n" (JSIL_Print.string_of_logic_expression le_pat_subst false)  (JSIL_Print.string_of_logic_expression le false); *)
			if (is_equal le_pat_subst le p_formulae gamma)
				then
					((* Printf.printf "I managed to UNIFY BABY!!!"; *)
					(true, None))
				else (false, None)
		with _ ->	(true, Some (var, le)))

	| LLit lit ->
		if (is_equal le_pat le p_formulae gamma)
			then (true, None)
			else (false, None)

	| LNone ->
		if (is_equal LNone le p_formulae gamma)
			then (true, None)
			else (false, None)

	| LUnknown ->
		if (is_equal LUnknown le p_formulae gamma)
			then (true, None)
			else (false, None)

	| _ ->
		let msg = Printf.sprintf "Illegal expression in pattern to unify. le_pat: %s. le: %s."
			(JSIL_Print.string_of_logic_expression le_pat false) (JSIL_Print.string_of_logic_expression le false) in
		raise (Failure msg)

let update_subst1 subst unifier =
	match unifier with
	| false, _ -> false
	| _, Some (var, le) ->
		 Hashtbl.add subst var le;
		true
	| _, None -> true

let update_subst2 subst unifier1 unifier2 p_formulae gamma =
	match unifier1, unifier2 with
	| (true, None), (true, None) -> true

	| (true, Some _), (true, None) -> update_subst1 subst unifier1

	| (true, None), (true, Some _) -> update_subst1 subst unifier2

	| (true, Some (var1, le1)), (true, Some (var2, le2)) ->
		if (var1 = var2)
			then
				begin
					if (is_equal le1 le2 p_formulae gamma)
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


let unify_fv_pair (pat_field, pat_value) (fv_list : (jsil_logic_expr * jsil_logic_expr) list) p_formulae gamma subst :  (((jsil_logic_expr * jsil_logic_expr) list) * (jsil_logic_expr * jsil_logic_expr)) option =
	(* Printf.printf "unify_fv_pair. pat_field: %s, pat_value: %s\n" (JSIL_Print.string_of_logic_expression pat_field false) (JSIL_Print.string_of_logic_expression pat_value false);
	Printf.printf "fv_list: %s\n" (JSIL_Memory_Print.string_of_symb_fv_list fv_list); *)
	let rec loop fv_list traversed_fv_list =
		match fv_list with
		| [] -> None
		| (e_field, e_value) :: rest ->
			let field_unifier = unify_lexprs pat_field e_field p_formulae gamma subst in
			let value_unifier = unify_lexprs pat_value e_value p_formulae gamma subst in
			if (update_subst2 subst field_unifier value_unifier p_formulae gamma)
				then
					Some ((traversed_fv_list @ rest), (e_field, e_value))
				else
					loop rest ((e_field, e_value) :: traversed_fv_list) in
	loop fv_list []


let unify_symb_fv_lists pat_fv_list fv_list def_val p_formulae gamma subst : (((jsil_logic_expr * jsil_logic_expr) list) * ((jsil_logic_expr * jsil_logic_expr) list)) option =
	(**
		let error_msg pat_field pat_val =
		let pat_field_str = JSIL_Print.string_of_logic_expression pat_field false in
		let pat_val_str = JSIL_Print.string_of_logic_expression pat_val false in
			Printf.sprintf "Field-val pair (%s, %s) in pattern has not been matched" pat_field_str pat_val_str in
	*)

	(* Printf.printf "Inside unify_symb_fv_lists. pat_fv_list: %s. fv_list: %s.\n" (JSIL_Memory_Print.string_of_symb_fv_list pat_fv_list) (JSIL_Memory_Print.string_of_symb_fv_list fv_list); *)

	let rec loop (fv_list : (jsil_logic_expr * jsil_logic_expr) list) (pat_list : (jsil_logic_expr * jsil_logic_expr) list) (matched_fv_list : (jsil_logic_expr * jsil_logic_expr) list) =
		match pat_list with
		| [] -> Some (fv_list, matched_fv_list)
		| (pat_field, pat_val) :: rest_pat_list ->
			let res = unify_fv_pair (pat_field, pat_val) fv_list p_formulae gamma subst in
			(match res with
			| None ->
				(* Printf.printf "I could NOT unify an fv-pair. pat_val: %s. def_val: %s\n" (JSIL_Print.string_of_logic_expression pat_val false) (JSIL_Print.string_of_logic_expression def_val false); *)
				(match def_val with
				| LUnknown -> None
				| _ ->
					let unifier = unify_lexprs pat_val def_val p_formulae gamma subst in
					if (update_subst1 subst unifier)
						then loop fv_list rest_pat_list matched_fv_list
						else None)
			| Some (rest_fv_list, matched_fv_pair) -> loop rest_fv_list rest_pat_list (matched_fv_pair :: matched_fv_list)) in
	loop fv_list pat_fv_list []


let make_all_different_pure_assertion fv_list_1 fv_list_2 : jsil_logic_assertion list =

	let rec all_different_field_against_fv_list f fv_list pfs : jsil_logic_assertion list =
		match fv_list with
		| [] -> pfs
		| (f', v') :: rest ->
			(match f, f' with
			| LLit _, LLit _ -> all_different_field_against_fv_list f rest pfs
			| _, _ -> all_different_field_against_fv_list f rest ((LNot (LEq (f, f'))) :: pfs)) in

	let rec all_different_fv_list_against_fv_list fv_list_1 fv_list_2 pfs : jsil_logic_assertion list =
		(match fv_list_1 with
		| [] -> pfs
		| (f, _) :: rest ->
			let new_pfs = all_different_field_against_fv_list f fv_list_2 pfs in
			all_different_fv_list_against_fv_list rest fv_list_2 new_pfs) in

	all_different_fv_list_against_fv_list fv_list_1 fv_list_2 []



let unify_symb_heaps (pat_heap : symbolic_heap) (heap : symbolic_heap) pure_formulae gamma (subst : substitution) : (symbolic_heap option) * ((jsil_logic_assertion list) option)  =
	let quotient_heap = LHeap.create 1021 in
	try
		let pfs : jsil_logic_assertion list =
			LHeap.fold
				(fun pat_loc (pat_fv_list, pat_def) pfs ->
					(match pat_def with
					| LUnknown ->
						let loc = try
							(match (Hashtbl.find subst pat_loc) with
							| LLit (Loc loc) -> loc
							| ALoc loc -> loc
				  		| _ -> pat_loc)
							with _ -> pat_loc in
						let fv_list, (def : jsil_logic_expr) =
							(try LHeap.find heap loc with _ ->
								let msg = Printf.sprintf "Location %s in pattern has not been matched" loc in
								raise (Failure msg)) in
						let fv_lists = unify_symb_fv_lists pat_fv_list fv_list def pure_formulae gamma subst in
						(match fv_lists with
						| Some (new_fv_list, matched_fv_list) ->
							LHeap.replace quotient_heap loc (new_fv_list, def);
							let new_pfs : jsil_logic_assertion list = make_all_different_pure_assertion new_fv_list matched_fv_list in
							new_pfs @ pfs
						| None -> raise (Failure ("Pattern heaps cannot have default values")))
					| _ -> raise (Failure ("Pattern heaps cannot have default values"))))
				pat_heap
				[] in
		LHeap.iter
			(fun loc (fv_list, def) ->
				try
					let _ = LHeap.find quotient_heap loc in
					()
				with _ ->
					LHeap.add quotient_heap loc (fv_list, def))
			heap;
		LHeap.iter
			(fun loc (fv_list, def) ->
				match def with
				| LUnknown ->
					if ((List.length fv_list) = 0)
						then LHeap.remove quotient_heap loc
				| _ -> ())
			quotient_heap;
		(Some quotient_heap), (Some pfs)
	with _ -> None, None


let unify_pred_against_pred (pat_pred : (string * (jsil_logic_expr list))) (pred : (string * (jsil_logic_expr list))) p_formulae gamma (subst : substitution) : substitution option =
	let pat_pred_name, pat_pred_args = pat_pred in
	let pred_name, pred_args = pred in

	(* Printf.printf "Trying to unify %s against %s\n" (JSIL_Memory_Print.string_of_pred pat_pred false) (JSIL_Memory_Print.string_of_pred pred false); *)
	let rec unify_expr_lists pat_list list subst =
		(match pat_list, list with
		| [], [] -> ( (* Printf.printf "Success in predicate set unification\n"; *) true)
		| (pat_le :: rest_pat_list), (le :: rest_list) ->
			let unifier = unify_lexprs pat_le le p_formulae gamma subst in
			(* Printf.printf "pat_le: %s. le: %s\n" (JSIL_Print.string_of_logic_expression pat_le false) (JSIL_Print.string_of_logic_expression le false); *)
			if (update_subst1 subst unifier)
				then unify_expr_lists rest_pat_list rest_list subst
				else ( (* Printf.printf "Tremendous failure in predicate set unification\n"; *) false)
		| _, _ -> false) in

	if (pat_pred_name = pred_name) then
		begin
		let new_subst = Hashtbl.copy subst in
		if (unify_expr_lists pat_pred_args pred_args new_subst)
			then Some new_subst
			else None
		end
		else None


let unify_pred_against_pred_set (pat_pred : (string * (jsil_logic_expr list))) (preds : (string * (jsil_logic_expr list)) list) p_formulae gamma (subst : substitution) =
	let rec loop preds quotient_preds =
		(match preds with
		| [] -> None, quotient_preds
		| pred :: rest_preds ->
			let new_subst = unify_pred_against_pred pat_pred pred p_formulae gamma subst in
			(match new_subst with
			| None -> loop rest_preds (pred :: quotient_preds)
			| Some new_subst -> Some new_subst, (quotient_preds @ rest_preds))) in
	loop preds []


let unify_pred_list_against_pred_list (pat_preds : (string * (jsil_logic_expr list)) list) (preds : (string * (jsil_logic_expr list)) list) p_formulae gamma (subst : substitution) =
	let rec loop pat_preds preds subst =
		(match pat_preds with
		| [] -> Some subst, preds
		| pat_pred :: rest_pat_preds ->
			let new_subst, rest_preds = unify_pred_against_pred_set pat_pred preds p_formulae gamma subst in
			(match new_subst with
			| None -> None, []
			| Some new_subst -> loop rest_pat_preds rest_preds new_subst)) in
	loop pat_preds preds subst


let unify_pred_arrays (pat_preds : predicate_set) (preds : predicate_set) p_formulae gamma (subst : substitution) =
	let pat_preds = DynArray.to_list pat_preds in
	let preds = DynArray.to_list preds in
	let new_subst, quotient_preds = unify_pred_list_against_pred_list pat_preds preds p_formulae gamma subst in
	new_subst, (DynArray.of_list quotient_preds)


let unify_gamma pat_gamma gamma pat_store subst ignore_vars =
  (* Printf.printf "I am about to unify two gammas\n";
	 	Printf.printf "pat_gamma: %s.\ngamma: %s.\nsubst: %s\n"
		(JSIL_Memory_Print.string_of_gamma pat_gamma) (JSIL_Memory_Print.string_of_gamma gamma)
		(JSIL_Memory_Print.string_of_substitution subst);  *)
	let res = (Hashtbl.fold
		(fun var v_type ac ->
			(* (not (is_lvar_name var)) *)
			(if ((not ac) || (List.mem var ignore_vars))
				then ac
				else
					try
						let le =
							(if (is_lvar_name var)
								then Hashtbl.find subst var
								else
									(match (store_get_var_val pat_store var) with
									| Some le -> JSIL_Logic_Utils.lexpr_substitution le subst true
									| None -> (PVar var))) in
						let le_type, is_typable = Entailment_Engine.normalised_is_typable gamma None le in
						match le_type with
						| Some le_type ->
							 (* Printf.printf "unify_gamma. pat gamma var: %s. le: %s. v_type: %s. le_type: %s\n"
								var
								(JSIL_Print.string_of_logic_expression le false)
								(JSIL_Print.string_of_type v_type)
								(JSIL_Print.string_of_type le_type); *)
							(le_type = v_type)
						| None ->
							 (* Printf.printf "failed unify_gamma. pat gamma var: %s. le: %s. v_type: %s\n"
								var
								(JSIL_Print.string_of_logic_expression le false)
								(JSIL_Print.string_of_type v_type); *)
							false
					with _ ->
						true))
		pat_gamma
		true) in
	(* Printf.printf "unify_gamma. res: %b\n" res; *)
	res



let is_symb_heap_empty heap =
	LHeap.fold
		(fun loc (fv_list, def) ac ->
			match fv_list with
			| [] -> ac
			| _ -> false)
		heap
		true

let is_preds_empty preds =
	(DynArray.length preds) = 0


let is_empty_symb_state symb_state =
	(is_symb_heap_empty (get_heap symb_state)) && (is_preds_empty (get_preds symb_state))


let spec_logic_vars_discharge subst lvars pf_list gamma =
	let pfs_to_prove =
		List.fold_left
			(fun ac var ->
				try
					let le = Hashtbl.find subst var in
					let new_pa =	(LEq ((LVar var), le)) in
					new_pa :: ac
				with _ ->  ac)
			[]
			lvars in
	let ret = Entailment_Engine.check_entailment [] pf_list pfs_to_prove gamma in
	(* Printf.printf "check if (%s) entails (%s) - ret: %b\n" (JSIL_Print.str_of_assertion_list pf_list) (JSIL_Print.str_of_assertion_list pfs_to_prove) ret;	*)
	ret


let pf_list_of_discharges discharges subst =
	let rec loop discharges pfs =
		match discharges with
		| [] -> pfs
		| (le_pat, le) :: rest_discharges ->
			let s_le_pat = JSIL_Logic_Utils.lexpr_substitution le_pat subst true in
			loop rest_discharges ((LEq (s_le_pat, le)) :: pfs) in
	loop discharges []


let unify_symb_states lvars existentials pat_symb_state (symb_state : symbolic_state) : (symbolic_heap * predicate_set * substitution * (jsil_logic_assertion list) * bool) option  =
	let pat_heap, pat_store, pat_pf, pat_gamma, pat_preds = pat_symb_state in
	let heap, store, pf, gamma, preds = symb_state in
	let subst = init_substitution lvars in
	(* Printf.printf "store: %s. pat_store: %s.\n\n" (JSIL_Memory_Print.string_of_shallow_symb_store store false) (JSIL_Memory_Print.string_of_shallow_symb_store pat_store false); *)
	let discharges = unify_stores pat_store store subst None (pfs_to_list pf) gamma in
	match discharges with
	| Some discharges ->
		let spec_vars_check = spec_logic_vars_discharge subst lvars (get_pf_list symb_state) (get_gamma symb_state) in
	  (* Printf.printf "unify_symb_states. heap:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_heap heap false); *)
		let (quotient_heap, new_pfs) : (symbolic_heap option) * ((jsil_logic_assertion list) option) = unify_symb_heaps pat_heap heap pf gamma subst in
		(* Printf.printf "Substitution afert heap unification baby!!!\n%s" (JSIL_Memory_Print.string_of_substitution subst); *)
		let new_subst, quotient_preds = unify_pred_arrays pat_preds preds pf gamma subst in
		(match spec_vars_check, new_subst, quotient_heap, new_pfs with
		| true, Some new_subst, Some quotient_heap, Some new_pfs ->
			let s_new_subst = copy_substitution new_subst in
			(* Printf.printf "I computed a quotient heap but I also need to check an entailment\n";
			Printf.printf "The quotient heap that I just computed:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_heap quotient_heap false);
			Printf.printf "the symbolic state after computing quotient heap:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state); *)

			let pf_discharges = pf_list_of_discharges discharges s_new_subst in
			let pat_pf_list =
				(List.map
					(fun a -> assertion_substitution a s_new_subst true)
					(pfs_to_list pat_pf)) in
			extend_pf pf new_pfs;
			let pf_list = pfs_to_list pf in
			let pat_pf_existentials = get_subtraction_vars pat_pf_list pf_list false in
			let new_pat_pf_existentials = (List.map (fun v -> fresh_lvar ()) pat_pf_existentials) in

			extend_substitution s_new_subst pat_pf_existentials (List.map (fun v -> LVar v) new_pat_pf_existentials);


			let existentials = new_pat_pf_existentials @ existentials in

			let new_gamma =
				if ((List.length pat_pf_existentials) > 0)
					then (
						let new_gamma = copy_gamma gamma in
						let new_pat_gamma = filter_gamma pat_gamma pat_pf_existentials s_new_subst in
						extend_gamma new_gamma new_pat_gamma;
						new_gamma)
				else gamma in

			let pat_pf_list = List.map (fun a -> assertion_substitution a s_new_subst true) pat_pf_list in
			let pf_discharges = List.map (fun a -> assertion_substitution a s_new_subst true) pf_discharges in

			let existentials_str = print_var_list existentials in
			(* Printf.printf "Dicharges: %s\n" (JSIL_Print.str_of_assertion_list pf_discharges);
			Printf.printf "About to check if (%s) ENTAILS (Exists %s. (%s))\n" (JSIL_Print.str_of_assertion_list pf_list) existentials_str (JSIL_Print.str_of_assertion_list (pat_pf_list @ pf_discharges));  *)
			let unify_gamma_check = (unify_gamma pat_gamma new_gamma pat_store s_new_subst existentials) in
			let entailment_check_ret = Entailment_Engine.check_entailment existentials pf_list (pat_pf_list @ pf_discharges)  new_gamma in
			(if (entailment_check_ret & unify_gamma_check) then
					((* Printf.printf "I could check the entailment!!!\n"; *)
					Some (quotient_heap, quotient_preds, s_new_subst, pf_discharges, true))
				else
					((* Printf.printf "I could NOT check the entailment!!!\n";
					Printf.printf "entailment_check_ret: %b. unify_gamma_check: %b.\n" entailment_check_ret unify_gamma_check; *)
					Some (quotient_heap, quotient_preds, new_subst, pf_discharges, false)))
		| _ -> None)
	| None -> None


let fully_unify_symb_state pat_symb_state symb_state lvars existentials =
	(* Printf.printf "fully_unify_symb_state. final symb_state:\n%s. Post symb_state:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state) (JSIL_Memory_Print.string_of_shallow_symb_state pat_symb_state); *)
	let unifier = unify_symb_states lvars existentials pat_symb_state symb_state in
	match unifier with
	| Some (quotient_heap, quotient_preds, subst, pf_discharges, true) ->
		if ((is_symb_heap_empty quotient_heap) && (is_preds_empty quotient_preds)) then
			(Some subst, "")
		else (None, "incomplete match")
	| Some (_, _, _, _, false)
	| None -> (None, "non_unifiable heaps")


let unify_symb_state_against_post proc_name spec symb_state flag symb_exe_info =
	let print_error_to_console msg =
		(if (msg = "")
			then Printf.printf "Failed to verify a spec of proc %s\n" proc_name
			else Printf.printf "Failed to verify a spec of proc %s -- %s\n" proc_name msg);
		let final_symb_state_str = JSIL_Memory_Print.string_of_shallow_symb_state symb_state in
		let post_symb_state_str = JSIL_Memory_Print.string_of_symb_state_list spec.n_post in
		Printf.printf "Final symbolic state: %s\n" final_symb_state_str;
		Printf.printf "Post condition: %s\n" post_symb_state_str in

	let rec loop posts post_vars_lists i =
		(match posts, post_vars_lists with
		| [], [] -> print_error_to_console "non_unifiable heaps";  raise (Failure "post condition is not unifiable")
		| post :: rest_posts, post_lvars :: rest_posts_lvars ->
			let subst = fully_unify_symb_state post symb_state spec.n_lvars post_lvars in
			(match subst with
			| Some subst, _ ->
				activate_post_in_post_prunning_info symb_exe_info proc_name i;
				Printf.printf "Verified one spec of proc %s\n" proc_name
			| None, _       -> loop rest_posts rest_posts_lvars (i + 1))) in

	loop spec.n_post spec.n_post_lvars 0


let merge_heaps heap new_heap p_formulae gamma =
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
							let _, fv_pair, i_am_sure_the_field_does_exist = find_field loc fv_list le_field p_formulae gamma in
							(match fv_pair, i_am_sure_the_field_does_exist with
							| None, true -> loop ((le_field, le_val) :: q_fv_list) rest_n_fv_list
							| None, false
							| Some _, _ ->
								(* Printf.printf "i_am_sure_the_field_does_exist: %b\n" i_am_sure_the_field_does_exist;*)
								raise (Failure "heaps non-mergeable"))) in
					let q_fv_list = loop [] n_fv_list in
					LHeap.replace heap loc (q_fv_list @ fv_list, def)
				with Not_found ->
					LHeap.add heap loc (n_fv_list, LUnknown))
			| _ -> raise (Failure "heaps non-mergeable: the default field is not unknwon!!!"))
		new_heap


let merge_gammas gamma_l gamma_r =
	Hashtbl.iter
		(fun var v_type ->
			if (not (Hashtbl.mem gamma_l var))
				then Hashtbl.add gamma_l var v_type)
		gamma_r


let merge_pfs pfs_l pfs_r = DynArray.append pfs_r pfs_l


let merge_symb_states symb_state_l symb_state_r subst  : symbolic_state =
	(* *)

	(* Printf.printf "gamma_r: %s\n." (JSIL_Memory_Print.string_of_gamma (get_gamma symb_state_r)); *)
	(* Printf.printf "substitution: %s\n" (JSIL_Memory_Print.string_of_substitution subst); *)

	let symb_state_r = symb_state_substitution symb_state_r subst false in
	let heap_l, store_l, pf_l, gamma_l, preds_l = symb_state_l in
	let heap_r, store_r, pf_r, gamma_r, preds_r = symb_state_r in

	DynArray.append pf_r pf_l;
	merge_gammas gamma_l gamma_r;

	(* Printf.printf "BEFORE MERGING HEAPS. pfs_l: %s\n. pfs_r: %s\n." (JSIL_Memory_Print.string_of_shallow_p_formulae pf_l false)
		(JSIL_Memory_Print.string_of_shallow_p_formulae pf_r false); *)
	merge_heaps heap_l heap_r pf_l gamma_l;
	(* Printf.printf "AFTER MERGING HEAPS\n\n"; *)

	DynArray.append preds_r preds_l;
	(* *)
	(* Printf.printf "s_heap_l after merge: %s.\ns_preds_l: %s.\ns_store_l: %s.\n" (JSIL_Memory_Print.string_of_shallow_symb_heap heap_l)
		(JSIL_Memory_Print.string_of_preds preds_l) (JSIL_Memory_Print.string_of_shallow_symb_store store_l); *)
	(* *)
	(heap_l, store_l, pf_l, gamma_l, preds_l)


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
		update_abs_heap_default heap new_loc LNone;
		update_abs_heap heap new_loc (LLit (String proto_f)) (LLit Null) pure_formulae gamma;
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
		let ne = abs_heap_find heap l ne2 pure_formulae gamma in
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
			update_abs_heap heap l ne2 ne3 pure_formulae gamma
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
		update_abs_heap heap l ne2 LNone pure_formulae gamma;
		LLit (Bool true)

	| SHasField (x, e1, e2) ->
		let ne1, t_le1, _ = safe_symb_evaluate_expr e1 store gamma pure_formulae in
		let ne2, t_le2, _ = safe_symb_evaluate_expr e2 store gamma pure_formulae in
		match ne1 with
		| LLit (Loc l)
		| ALoc l ->
			let res = abs_heap_check_field_existence heap l ne2 pure_formulae gamma in
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


let proc_get_ret_var proc ret_flag =
	let ret_var =
		match ret_flag with
		| Normal -> proc.ret_var
		| Error -> proc.error_var in
	match ret_var with
	| Some ret_var -> ret_var
	| None -> raise (Failure "proc_get_ret_var: fatal error")

let store_get_var store var =
	(try
		Hashtbl.find store var
	with _ ->
		let msg = Printf.sprintf "store_get_var: fatal error. var: %s" var in
		raise (Failure msg))


let get_proc prog proc_name =
	try
		Hashtbl.find prog proc_name
	with _ ->
		raise (Failure "get_proc: fatal error")


let get_proc_args proc = proc.proc_params

let symb_state_replace_store symb_state new_store =
	let heap, _, pfs, gamma, preds = symb_state in
	(heap, new_store, pfs, gamma, preds)


let symb_state_replace_heap symb_state new_heap =
	let _, store, pfs, gamma, preds = symb_state in
	(new_heap, store, pfs, gamma, preds)



let symb_state_replace_preds symb_state new_preds =
	let heap, store, pfs, gamma, _ = symb_state in
	(heap, store, pfs, gamma, new_preds)


let get_proc_cmd proc i =
	proc.proc_body.(i)



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
			let new_symb_state = merge_symb_states new_symb_state post subst in
			let ret_lexpr = store_get_var (get_store post) ret_var in
			let ret_lexpr = JSIL_Logic_Utils.lexpr_substitution ret_lexpr subst false in
			new_symb_state, ret_flag, ret_lexpr in

		extend_symb_state_with_pfs symb_state pf_discharges;
		let symb_state = symb_state_replace_heap symb_state quotient_heap in
		let symb_state = symb_state_replace_preds symb_state quotient_preds in
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
		let pfs = pf_substitution pre_pfs subst false in
		let gamma = gamma_substitution pre_gamma subst false in
		merge_gammas gamma (get_gamma symb_state);
		merge_pfs pfs (get_pf symb_state);
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
			let unifier = unify_symb_states [] [] spec.n_pre symb_state_aux in
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
			let unifier = unify_symb_states [] [] pred_def symb_state_aux in
			(match unifier with
			| Some (quotient_heap, quotient_preds, subst, pf_discharges, true) ->
			  (* Printf.printf "I can fold this!!!\n"; *)
				let symb_state = symb_state_replace_heap symb_state quotient_heap in
				let symb_state = symb_state_replace_preds symb_state quotient_preds in
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
	let subst0 = subtract_pred pred_name args (get_preds symb_state) (get_pf symb_state) (get_gamma symb_state) spec_vars in
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
			let discharges = unify_stores pat_store store pat_subst (Some subst) (pfs_to_list (get_pf symb_state)) (get_gamma symb_state) in
			(match discharges with
			| Some discharges ->
					(* Printf.printf "Current pred symbolic state: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_state pred_symb_state); *)
					(*Printf.printf "I need to apply the following subst in the current symbolic store: %s\n"
						(JSIL_Memory_Print.string_of_substitution subst);
					Printf.printf "I need to apply the following subst in the pattern symbolic store: %s\n"
						(JSIL_Memory_Print.string_of_substitution pat_subst); *)
					let new_symb_state : symbolic_state = copy_symb_state symb_state in
					let (new_symb_state : symbolic_state) = symb_state_substitution new_symb_state subst true in
					symb_state_add_subst_as_equalities new_symb_state subst (get_pf new_symb_state) spec_vars;
					(* Printf.printf "Symbolic state after substitution: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_state new_symb_state);
					Printf.printf "Pred Symb_sate:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state pred_symb_state);
					Printf.printf " subst: %s pat_subst: %s\n" (JSIL_Memory_Print.string_of_substitution subst) (JSIL_Memory_Print.string_of_substitution pat_subst); *)
					let pat_subst = compose_partial_substitutions subst pat_subst in
					let unfolded_symb_state = merge_symb_states new_symb_state pred_symb_state pat_subst in
					(* Printf.printf "pred symbolic state at the middle: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_state pred_symb_state); *)
					let spec_vars_subst = filter_substitution subst spec_vars in

					let pf = get_pf unfolded_symb_state in
					let gamma =  (get_gamma unfolded_symb_state) in
					let new_pfs = pf_of_substitution spec_vars_subst in
					let new_pfs_subst0 = pf_of_substitution subst0 in
					let pf_discharges = pf_list_of_discharges discharges pat_subst in

					extend_pf pf new_pfs;
					extend_pf pf new_pfs_subst0;
					extend_pf pf pf_discharges;

					JSIL_Logic_Normalise.extend_typing_env_using_assertion_info new_pfs gamma;
					JSIL_Logic_Normalise.extend_typing_env_using_assertion_info new_pfs_subst0 gamma;
					JSIL_Logic_Normalise.extend_typing_env_using_assertion_info pf_discharges gamma;

					(* Printf.printf "The discharges to prove are: %s\n" (JSIL_Print.str_of_assertion_list pf_discharges); *)
					(* Printf.printf "I unfolded the following symbolic state:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state unfolded_symb_state); *)
					let satisfiability_check = Entailment_Engine.check_satisfiability (get_pf_list unfolded_symb_state) gamma [] in
					(* let discharges_check = Entailment_Engine.check_entailment [] pf pf_discharges gamma in *)
					if (satisfiability_check)
						then (
							(* Printf.printf "Checked the pure part of the unfolding!!"; *)
							loop rest_pred_defs (unfolded_symb_state :: symb_states))
						else (
							(* Printf.printf "Could NOT check the pure part of the unfolding. satisfiability_check: %b.\n" satisfiability_check;
							Printf.printf "pf_discharges: %s\n" (JSIL_Print.str_of_assertion_list pf_discharges); *)
							loop rest_pred_defs symb_states)
			| None -> loop rest_pred_defs symb_states)) in

	loop pred_defs []





let get_pred pred_tbl pred_name =
	try
		Hashtbl.find pred_tbl pred_name
	with _ ->
		let msg = Printf.sprintf "Predicate %s does not exist" pred_name in
		raise (Failure msg)

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


(* Information generated by the symbolic execution *)

let create_info_node_aux symb_state new_node_number cmd_index cmd_str =
	let heap_str = JSIL_Memory_Print.string_of_shallow_symb_heap (get_heap symb_state) true in
	let store_str = JSIL_Memory_Print.string_of_shallow_symb_store (get_store symb_state) true in
	let pfs_str = JSIL_Memory_Print.string_of_shallow_p_formulae (get_pf symb_state) true in
	let gamma_str = JSIL_Memory_Print.string_of_gamma (get_gamma symb_state) in
	let preds_str = JSIL_Memory_Print.string_of_preds (get_preds symb_state) true in
	let new_node_info =
		{
			heap_str = heap_str;
			store_str = store_str;
			pfs_str = pfs_str;
			gamma_str = gamma_str;
			preds_str = preds_str;
			(* cmd index *)
			cmd_index = cmd_index;
			cmd_str = cmd_str;
			(* node number *)
			node_number = new_node_number
		} in
	new_node_info

(* registering info nodes *)
let register_new_node_aux2 search_info new_node_info =
	let new_node_number = !(search_info.next_node) in
	search_info.next_node := new_node_number + 1;
	Hashtbl.add (search_info.info_nodes) new_node_number new_node_info;
	Hashtbl.replace search_info.info_edges new_node_info.node_number []

let register_new_node_aux search_info new_node_info parent_node_info =
	register_new_node_aux2 search_info new_node_info;
	try
	let parent_children = Hashtbl.find search_info.info_edges parent_node_info.node_number in
	Hashtbl.replace search_info.info_edges parent_node_info.node_number ((new_node_info.node_number) :: parent_children)
	with _ -> Printf.printf "What are you DOING??????\n\n"

let register_new_node search_info new_node_info =
	let parent_node_info = search_info.cur_node_info in
	register_new_node_aux search_info new_node_info parent_node_info


(** Creating info nodes and registering them *)
let create_info_node_aux2 symb_state search_info msg i =
	let new_node_number : int = !(search_info.next_node) in
	let i =
		match i with
		| None -> (-1)
		| Some i -> i in
	let new_node_info = create_info_node_aux symb_state new_node_number i msg in
	register_new_node search_info new_node_info;
	new_node_info


(* creating info nodes from the symbolic execution *)

let create_info_node_from_cmd search_info symb_state cmd i =
	let cmd_str = JSIL_Print.string_of_cmd_aux cmd i false true "" in
	create_info_node_aux2 symb_state search_info cmd_str (Some i)


let create_info_node_from_lcmd search_info symb_state lcmd =
	let cmd_str = JSIL_Print.string_of_logic_command lcmd true in
	create_info_node_aux2 symb_state search_info cmd_str None


let create_info_node_from_post search_info symb_state ret_flag success : unit =
	let msg = ("Postcondition. Ret flag: " ^
		(match ret_flag with
		| Normal -> "NORMAL"
		| Error -> "ERROR")) in
	let symb_state = List.nth symb_state 0 in
	if (success)
		then (create_info_node_aux2 symb_state search_info msg None; ())
		else
			begin
			let new_node_number : int = !(search_info.next_node) in
			let new_node_info : search_info_node = create_info_node_aux symb_state new_node_number (-1) msg in
			register_new_node_aux2 search_info new_node_info
			end


let create_info_node_from_error search_info error_msg =
	let new_node_number : int = !(search_info.next_node) in
	let msg = "ERROR: " ^ (String.escaped error_msg) in
	let new_node_info =
		{
			heap_str = "";
			store_str = "";
			pfs_str = "";
			gamma_str = "";
			preds_str = "";
			(* cmd index *)
			cmd_index = (-2);
			cmd_str = msg;
			(* node number *)
			node_number = new_node_number
		} in
	let parent_node =
		try Hashtbl.find search_info.info_nodes (new_node_number - 1)
			with _ -> raise (Failure "create_info_node_from_error: CORE FAILED") in
	register_new_node_aux search_info new_node_info parent_node;
	new_node_info

let create_info_node_from_invariant search_info symb_state post =
	let msg = if (post) then "Postcondition" else "Invariant" in
	let new_node_number : int = !(search_info.next_node) in
	let new_node_info = create_info_node_aux symb_state new_node_number (-1) msg in
	register_new_node search_info new_node_info;
	new_node_info



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

		if (Entailment_Engine.check_entailment [] (get_pf_list symb_state) a_le_then (get_gamma symb_state)) then
			(Printf.printf "in the THEN branch\n";
			symb_evaluate_next_cmd s_prog proc spec search_info symb_state i j)
			else (if (Entailment_Engine.check_entailment [] (get_pf_list symb_state) a_le_else (get_gamma symb_state)) then
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
				let ret_type, _ = Entailment_Engine.normalised_is_typable (get_gamma symb_state) (Some (get_pf symb_state)) ret_le in
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
		(unify_symb_state_against_post proc.proc_name spec symb_state Normal search_info;
		create_info_node_from_post search_info spec.n_post Normal true; ())
	else (if ((Some cur) = proc.error_label) then
		(unify_symb_state_against_post proc.proc_name spec symb_state Error search_info;
		create_info_node_from_post search_info spec.n_post Error true; ())
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
						(match (fully_unify_symb_state new_symb_state symb_state spec.n_lvars [ ]) with
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
							(match (fully_unify_symb_state new_symb_state symb_state spec.n_lvars [ ]) with
							| Some _, _ -> new_symb_state
							| None, msg -> raise (Failure msg)) in


					let symb_states = symb_evaluate_logic_cmds s_prog metadata.logic_cmds [ symb_state ] spec.n_subst spec.n_lvars in
					(* Printf.printf "I unfolded everything that needed to be unfolded!!!!\n"; *)
					let len = List.length symb_states in
					List.iter
						(fun symb_state ->
							let vis_tbl = if (len > 1) then (copy_vis_tbl search_info.vis_tbl) else search_info.vis_tbl in
							let info_node = create_info_node_from_cmd search_info symb_state cmd next in
							let new_search_info = udpdate_search_info search_info info_node vis_tbl in
							symb_evaluate_cmd s_prog proc spec new_search_info symb_state next)
						symb_states
				end
		end)


let symb_evaluate_proc s_prog proc_name spec i prunning_info =
	let node_info = create_info_node_aux spec.n_pre 0 (-1) "Precondition" in
	let search_info = make_symb_exe_search_info node_info prunning_info i in

	let proc = get_proc s_prog.program proc_name in
	let sep_str = "---------------------------------------------------\n" in

	if (!verbose) then Printf.printf "%s" (sep_str ^ sep_str ^ sep_str ^ "Symbolic execution of " ^ proc_name ^ "\n");
	let success, failure_msg =
		(try
			symb_evaluate_next_cmd s_prog proc spec search_info spec.n_pre (-1) 0;
			true, None
		with Failure msg ->
			(Printf.printf "The EVALUATION OF THIS PROC GAVE AN ERROR: %d!!!!\n" i;
			create_info_node_from_error search_info msg;
			create_info_node_from_post search_info spec.n_post spec.n_ret_flag false;
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
	let results_str, dot_graphs = JSIL_Memory_Print.string_of_symb_exe_results results in
	results_str, dot_graphs
