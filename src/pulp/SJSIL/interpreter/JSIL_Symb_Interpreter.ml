open Entailment_Engine
open JSIL_Syntax
open JSIL_Memory_Model
open JSIL_Logic_Utils

let verbose = ref false

let proto_f = "@proto"



let pf_substitution pf_r subst = 
	let len = (DynArray.length pf_r) - 1 in 
	for i=0 to len do 
		let a = DynArray.get pf_r i in 
		let s_a = assertion_substitution a subst true in 
		DynArray.set pf_r i s_a 
	done	


let fv_list_substitution fv_list subst = 
	List.map 
		(fun (le_field, le_val) -> 
			let s_le_field = lexpr_substitution le_field subst true in 
			let s_le_val = lexpr_substitution le_val subst true in 
			(s_le_field, s_le_val))
		fv_list


let heap_substitution (heap : symbolic_heap) (subst : (string, jsil_logic_expr) Hashtbl.t) = 
	let new_heap = LHeap.create 1021 in 
	LHeap.iter 
		(fun loc (fv_list, def) -> 
			let s_loc = 
				(try 
					(match (Hashtbl.find subst loc) with 
					| LLit (Loc loc) -> loc 
					| ALoc loc -> loc 
					| _ -> loc)
				 with _ -> loc) in  
			let s_fv_list = fv_list_substitution fv_list subst in 
			let s_def = lexpr_substitution def subst true in
			LHeap.add new_heap s_loc (s_fv_list, s_def))
		heap; 
	new_heap
			

let rec gamma_substitution gamma subst = 
	let new_gamma = Hashtbl.create 31 in 
	Hashtbl.iter 
		(fun var v_type -> 
			try 
			let new_var = Hashtbl.find subst var in 
			(match new_var with 
			| LVar new_var -> Hashtbl.replace new_gamma new_var v_type
			| _ -> ())
			with _ -> ())
		gamma; 
	new_gamma


let pred_substitution pred subst = 
	let pred_name, les = pred in 
	let s_les = List.map (fun le -> lexpr_substitution le subst true)  les in 
	(pred_name, s_les) 


let preds_substitution preds subst = 
	let len = DynArray.length preds in 
	let new_preds = DynArray.make len in 
	for i=0 to len - 1 do 
		let pred = DynArray.get preds i in 
		let s_pred = pred_substitution pred subst in 
		DynArray.set new_preds i s_pred 
	done; 
	new_preds

let rec safe_symb_evaluate_expr (expr : jsil_expr) store gamma = 
	let nle = symb_evaluate_expr expr store gamma in 
	let nle_type, is_typable = JSIL_Logic_Normalise.normalised_is_typable gamma nle in 
	if (is_typable) 
		then nle, nle_type, is_typable 
		else 
			begin 
				let gamma_str = JSIL_Memory_Print.string_of_gamma gamma in 
				let msg = Printf.sprintf "The logical expression %s is not typable in the typing enviroment: %s" (JSIL_Print.string_of_logic_expression nle false) gamma_str in
				raise (Failure msg)  
			end
and 
symb_evaluate_expr (expr : jsil_expr) store gamma = 
	match expr with 
	| Literal lit -> LLit lit
	
	| Var var -> 
		(try Hashtbl.find store var 
		with _ -> 
			let msg = Printf.sprintf "Variable %s not found in logical store." var in 
			raise (Failure msg))
	
	| BinOp (e1, op, e2) ->
		let nle1, _, _ = safe_symb_evaluate_expr e1 store gamma in 
		let nle2, _, _ = safe_symb_evaluate_expr e2 store gamma in 
		(match nle1, nle2 with
		| LLit l1, LLit l2 -> 
			let l = JSIL_Interpreter.evaluate_binop op l1 l2 in 
			LLit l
		| _, _ -> LBinOp (nle1, op, nle2))
	
	| UnaryOp (op, e) -> 
		let nle, _, _ = safe_symb_evaluate_expr e store gamma in
		(match nle with 
		| LLit lit -> LLit (JSIL_Interpreter.evaluate_unop op lit)
		| _ -> LUnOp (op, nle))
	
	| VRef (e1, e2) ->
		let nle1, _, _ = safe_symb_evaluate_expr e1 store gamma in 
		let nle2, _, _ = safe_symb_evaluate_expr e2 store gamma in 
		(match nle1, nle2 with 
		| LLit l, LLit (String field) -> LLit (LVRef (l, field))
		| _, _ -> LEVRef (nle1, nle2))
	
	| ORef (e1, e2) ->
		let nle1, _, _ = safe_symb_evaluate_expr e1 store gamma in 
		let nle2, _, _ = safe_symb_evaluate_expr e2 store gamma in 
		(match nle1, nle2 with 
		| LLit l, LLit (String field) -> LLit (LORef (l, field))
		| _, _ -> LEORef (nle1, nle2))
	
	| Base	(e) -> 
		let nle, _, _ = safe_symb_evaluate_expr e store gamma in 
		(match nle with 
		| LLit (LVRef (l, _)) 
		| LLit (LORef (l, _)) -> LLit l
		| LEVRef (eb, _) 
		| LEORef (eb, _) -> eb
		| _ -> LBase (nle))
	
	| Field	(e) -> 
		let nle, _, _ = safe_symb_evaluate_expr e store gamma in 
		(match nle with 
		| LLit (LVRef (_, f)) 
		| LLit (LORef (_, f)) -> LLit (String f)
		| LEVRef (_, fe) 
		| LEORef (_, fe) -> fe
		| _ -> LField (nle))	
	
	| TypeOf (e) -> 
		let nle, _, _ = safe_symb_evaluate_expr e store gamma in 
		(match nle with 
		| LLit llit -> LLit (Type (JSIL_Interpreter.evaluate_type_of llit)) 
		| LNone -> raise (Failure "Illegal Logic Expression: TypeOf of None")
		| PVar _ -> raise (Failure "This should never happen: program variable in normalized expression") 
		| LVar var 
		| ALoc var -> 
			(try 
				let var_type = Hashtbl.find gamma var in 
				LLit (Type var_type)
			with _ -> LTypeOf (nle))
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
					let nle, _, _ = safe_symb_evaluate_expr e store gamma in 
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
		if all_literals 
			then LLit (LList lits)
			else LEList les 
	
	| LstNth (e1, e2) ->
		let list, _, _ = safe_symb_evaluate_expr e1 store gamma in
		let index, _, _ = safe_symb_evaluate_expr e2 store gamma in
		(match list, index with 
		| LLit (LList list), LLit (Num n) -> 
			(try (LLit (List.nth list (int_of_float n))) with _ -> 
					raise (Failure "List index out of bounds"))
		
		| LEList list, LLit (Num n) ->
			(try (List.nth list (int_of_float n)) with _ -> 
					raise (Failure "List index out of bounds"))
				
		| _, _ -> LLstNth (list, index))
	
	| StrNth (e1, e2) ->
		let str, _, _ = safe_symb_evaluate_expr e1 store gamma in
		let index, _, _ = safe_symb_evaluate_expr e2 store gamma  in
		(match str, index with 
		| LLit (String s), LLit (Num n) -> 
			LLit (String (String.make 1 (String.get s (int_of_float n))))
				
		| _, _ -> LStrNth (str, index))
	
	| _ -> raise (Failure "not supported yet")


let rec lift_logic_expr lexpr = 
	let f = lift_logic_expr in 
	(match lexpr with 
	| LBinOp (le1, op, le2) -> lift_binop_logic_expr op le1 le2 
	| LUnOp (op, le) -> lift_unop_logic_expr op le
	| LLit (Bool true) -> None, Some LTrue 
	| LLit (Bool false) -> None, Some LFalse 
	| _ -> Some lexpr, None)
and lift_binop_logic_expr op le1 le2 = 
	let err_msg = "logical expression cannot be lifted to assertion" in 
	let f = lift_logic_expr in 
	let lexpr_to_ass_binop binop = 
		(match binop with 
		| Equal -> (fun le1 le1 -> LEq (le1, le2))
		| LessThan -> (fun le1 le1 -> LLess (le1, le2)) 
		| LessThanString -> (fun le1 le1 -> LStrLess (le1, le2))  
		| LessThanEqual -> (fun le1 le1 -> LLessEq (le1, le2)) 
		| _ -> raise (Failure "Error: lift_binop_expr")) in  
	(match op with 
	| Equal 
	| LessThan
	| LessThanString
	| LessThanEqual -> 
		let l_op_fun = lexpr_to_ass_binop op in 
		(match ((f le1), (f le2)) with 
		| ((Some le1, None), (Some le2, None)) -> None, Some (l_op_fun le1 le2)
		| (_, _) -> raise (Failure err_msg)) 
	| And -> 
		(match ((f le1), (f le2)) with 
		| ((None, Some a1), (None, Some a2)) -> None, Some (LAnd (a1, a2))
		| (_, _) -> raise (Failure err_msg))
	| Or -> 
		(match ((f le1), (f le2)) with 
		| ((None, Some a1), (None, Some a2)) -> None, Some (LOr (a1, a2))
		| (_, _) -> raise (Failure err_msg))
	| _ -> Some (LBinOp (le1, op, le2)), None) 
and lift_unop_logic_expr op le = 
	let f = lift_logic_expr in
	let err_msg = "logical expression cannot be lifted to assertion" in 
	(match op with 
	| Not -> 
		(match (f le) with 
		| (None, Some a) -> None, Some (LNot a)
		| (_, _) -> raise (Failure err_msg)) 		
	| _ -> Some (LUnOp (op, le)), None)

let isEqual e1 e2 pure_formulae gamma = 
	match e1, e2 with 
	| LLit l1, LLit l2 -> l1 = l2
	| ALoc aloc1 , ALoc aloc2 -> aloc1 = aloc2
	| LNone, LNone -> true
	| LUnknown, LUnknown -> false
	| LVar x1, LVar x2 -> x1 = x2
	| _, _ -> Entailment_Engine.check_entailment (DynArray.to_list pure_formulae) [ (LEq (e1, e2)) ] gamma

let isDifferent e1 e2 pure_formulae gamma = 
	match e1, e2 with 
	| LLit l1, LLit l2 -> (not (l1 = l2)) 
	| ALoc aloc1, ALoc aloc2 -> (not (aloc1 = aloc2))
	| _, _ -> Entailment_Engine.check_entailment (DynArray.to_list pure_formulae) [ (LNot (LEq (e1, e2))) ] gamma 

(**
  find_field fv_list e p_formulae = fv_list', (e1, e2)
	   st: 
		    fv_list = fv_list' U (e1, e2)  
				and 
				pure_formulae |=
					
*)
let find_field fv_list e p_formulae gamma = 
	let rec find_field_rec fv_list traversed_fv_list = 
		match fv_list with 
		| [] -> traversed_fv_list, None 
		| (e_field, e_value) :: rest ->
			(if (isEqual e e_field p_formulae gamma)
				then traversed_fv_list @ rest, Some (e_field, e_value)
				else 
					(if (isDifferent e e_field p_formulae gamma)
						then find_field_rec rest ((e_field, e_value) :: traversed_fv_list)
						else 
							let e_str = JSIL_Print.string_of_logic_expression e false  in  
							let msg = Printf.sprintf "I cannot decide whether or not the field denoted by %s already exists in the symbolic heap" e_str in   
							raise (Failure msg))) in 
	find_field_rec fv_list []


let update_abs_heap_default (heap : symbolic_heap) loc e =
	let fv_list, default_val = try LHeap.find heap loc with _ -> [], LUnknown in 
	match default_val with 
	| LUnknown -> LHeap.replace heap loc (fv_list, e)    
 	| _ -> raise (Failure "the default value for the fields of a given object cannot be changed once set") 


let update_abs_heap (heap : symbolic_heap) loc e_field e_val p_formulae gamma =
	(* Printf.printf "Update Abstract Heap\n"; *)
	let fv_list, default_val = try LHeap.find heap loc with _ -> [], LUnknown in 
	let unchanged_fv_list, _ = find_field fv_list e_field p_formulae gamma in 
	LHeap.replace heap loc ((e_field, e_val) :: unchanged_fv_list, default_val)    


let abs_heap_find heap l e p_formulae gamma = 
	let fv_list, default_val = try LHeap.find heap l with _ -> [], LUnknown in 
	let _, field_val_pair = find_field fv_list e p_formulae gamma in
	match field_val_pair with 
	| Some (_, f_val) -> f_val
	| None -> default_val

let abs_heap_check_field_existence heap l e p_formulae gamma = 
	let f_val = abs_heap_find heap l e p_formulae gamma in 
	Printf.printf "abs_heap_check_field_existence found %s\n" (JSIL_Print.string_of_logic_expression f_val false); 
	match f_val with 
	| LUnknown -> None
	| LNone -> Some false 
	|	_ ->
		if (isEqual f_val LNone p_formulae gamma) then 
			(Some false)
			else (if (isDifferent f_val LNone p_formulae gamma) then
				(Some true)
				else None)

let abs_heap_delete heap l e p_formulae gamma = 
	let fv_list, default_val = try LHeap.find heap l with _ -> [], LUnknown in 
	let rest_fv_pairs, del_fv_pair = find_field fv_list e p_formulae gamma in
	match del_fv_pair with 
	| Some (_, _) -> LHeap.replace heap l (rest_fv_pairs, default_val) 
	| None -> raise (Failure "Trying to delete an inexistent field") 
		
		
let unify_stores (pat_store : symbolic_store) (store : symbolic_store) (subst : substitution) : bool = 
	try 
		Hashtbl.iter 
			(fun var pat_lexpr ->
				let lexpr = try Hashtbl.find store var with _ -> raise (Failure "the stores are not unifiable") in 
				match pat_lexpr, lexpr with
			
				| LLit pat_lit, LLit lit -> 
					if (lit = pat_lit) 
						then () 
						else raise (Failure "the stores are not unifiable") 
					 
				| ALoc pat_aloc, ALoc aloc -> Hashtbl.replace subst pat_aloc (ALoc aloc)  
				
				| LVar lvar, _ -> Hashtbl.replace subst lvar lexpr  
						
				| _, _ -> raise (Failure "the pattern store is not normalized."))
			pat_store;
		true
	with _ -> false


let unify_lexprs le_pat (le : jsil_logic_expr) p_formulae (gamma: typing_environment) (subst : (string, jsil_logic_expr) Hashtbl.t) : (bool * ((string * jsil_logic_expr) option)) = 
	match le_pat with 
	| LVar var 
	| ALoc var ->  
		(try 
			if (isEqual (Hashtbl.find subst var) le p_formulae gamma)
				then (true, None)
				else (false, None)	
		with _ ->	(true, Some (var, le))) 
			
	| LLit lit -> 
		if (isEqual le_pat le p_formulae gamma) 
			then (true, None)
			else (false, None)
	
	| LNone -> 
		if (isEqual LNone le p_formulae gamma)
			then (true, None)
			else (false, None)

	| LUnknown -> 
		if (isEqual LUnknown le p_formulae gamma)
			then (true, None)
			else (false, None)
			
	| _ -> raise (Failure "Illegal expression in pattern to unify")

let update_subst1 subst unifier = 
	match unifier with 
	| false, _ -> false
	| _, Some (var, le) -> Hashtbl.add subst var le; true 
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
					if (isEqual le1 le2 p_formulae gamma) 
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


let unify_fv_pair (pat_field, pat_value) (fv_list : (jsil_logic_expr * jsil_logic_expr) list) p_formulae gamma subst :  (jsil_logic_expr * jsil_logic_expr) list option = 
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
					Some (traversed_fv_list @ rest)
				else
					loop rest ((e_field, e_value) :: traversed_fv_list) in
	loop fv_list []


let unify_symb_fv_lists pat_fv_list fv_list def_val p_formulae gamma subst : (jsil_logic_expr * jsil_logic_expr) list option = 
	(** 
		let error_msg pat_field pat_val = 
		let pat_field_str = JSIL_Print.string_of_logic_expression pat_field false in 
		let pat_val_str = JSIL_Print.string_of_logic_expression pat_val false in 
			Printf.sprintf "Field-val pair (%s, %s) in pattern has not been matched" pat_field_str pat_val_str in
	*)
	
	(* Printf.printf "Inside unify_symb_fv_lists. pat_fv_list: %s. fv_list: %s.\n" (JSIL_Memory_Print.string_of_symb_fv_list pat_fv_list) (JSIL_Memory_Print.string_of_symb_fv_list fv_list); *)
	
	let rec loop (fv_list : (jsil_logic_expr * jsil_logic_expr) list) (pat_list : (jsil_logic_expr * jsil_logic_expr) list) = 
		match pat_list with 
		| [] -> Some fv_list 
		| (pat_field, pat_val) :: rest_pat_list -> 
			let rest_fv_list = unify_fv_pair (pat_field, pat_val) fv_list p_formulae gamma subst in 
			(match rest_fv_list with
			| None -> 
				(* Printf.printf "I could NOT unify an fv-pair. pat_val: %s. def_val: %s\n" (JSIL_Print.string_of_logic_expression pat_val false) (JSIL_Print.string_of_logic_expression def_val false); *) 
				(match def_val with 
				| LUnknown -> None
				| _ ->
					let unifier = unify_lexprs pat_val def_val p_formulae gamma subst in 
					if (update_subst1 subst unifier) 
						then loop fv_list rest_pat_list
						else None)
			| Some rest_fv_list -> loop rest_fv_list rest_pat_list) in  
	loop fv_list pat_fv_list
		
		
let unify_symb_heaps (pat_heap : symbolic_heap) (heap : symbolic_heap) pure_formulae gamma (subst : substitution) : symbolic_heap option = 
	let quotient_heap = LHeap.create 1021 in 
	try 
		LHeap.iter 
			(fun pat_loc (pat_fv_list, pat_def) -> 
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
					let new_fv_list = unify_symb_fv_lists pat_fv_list fv_list def pure_formulae gamma subst in
					(match new_fv_list with 
					| Some new_fv_list -> LHeap.replace quotient_heap loc (new_fv_list, def)
					| None -> raise (Failure ("Pattern heaps cannot have default values")))
				| _ -> raise (Failure ("Pattern heaps cannot have default values"))))
			pat_heap;
		Some quotient_heap
	with _ -> None


let unify_pred_against_pred (pat_pred : (string * (jsil_logic_expr list))) (pred : (string * (jsil_logic_expr list))) p_formulae gamma (subst : substitution) : substitution option = 
	let pat_pred_name, pat_pred_args = pat_pred in 
	let pred_name, pred_args = pred in
	
	Printf.printf "Trying to unify %s against %s\n" (JSIL_Memory_Print.string_of_pred pat_pred) (JSIL_Memory_Print.string_of_pred pred);
	
	let rec unify_expr_lists pat_list list subst = 
		(match pat_list, list with 
		| [], [] -> true 
		| (pat_le :: rest_pat_list), (le :: rest_list) -> 
			let unifier = unify_lexprs pat_le le p_formulae gamma subst in 
			if (update_subst1 subst unifier) 
				then unify_expr_lists rest_pat_list rest_list subst 
				else false
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

let unify_gamma pat_gamma gamma subst =
	Printf.printf "I am about to unify two gammas\n";
	Printf.printf "pat_gamma: %s.\ngamma: %s\n" (JSIL_Memory_Print.string_of_gamma pat_gamma) (JSIL_Memory_Print.string_of_gamma gamma);
	let res = (Hashtbl.fold 	
		(fun var v_type ac ->
			(if (not ac) 
				then ac 
				else 
					let le = try Hashtbl.find subst var with _ -> (LVar var) in
					let le_type, is_typable = JSIL_Logic_Normalise.normalised_is_typable gamma le in  
					if is_typable then 
						(match le_type with 
						| Some le_type -> le_type = v_type 
						| None -> (Printf.printf "I could not unify the gammas\n"; false))
						else (Printf.printf "I could not unify the gammas\n"; false)))
		pat_gamma 
		true) in 
	Printf.printf "I could unify the gammas!\n"; 
	true


let check_entailment_pf pf pat_pf gamma subst = 
	(* Printf.printf "I am inside the check entailment patati patata\n"; *)
	
	let str_of_assertion_list a_list = 
		List.fold_left 
			(fun ac a -> 
				let a_str = JSIL_Print.string_of_logic_assertion a false in 
				if (ac = "") then a_str else (ac ^ ", " ^ a_str))
			""
			a_list in 
	
	let pf_list = DynArray.to_list pf in 
	let pat_pf_list = 
		(List.map 
			(fun a -> assertion_substitution a subst true) 
			(DynArray.to_list pat_pf)) in 
			
	Printf.printf "About to check if (%s) entails (%s)\n" (str_of_assertion_list pf_list) (str_of_assertion_list pat_pf_list); 
	if (Entailment_Engine.check_entailment pf_list pat_pf_list gamma) then 
		(Printf.printf "The entailment holds!!!\n"; true)
		else (Printf.printf "The entailment does NOT hold!!!\n"; false)
		
						
let unify_symb_states lvars pat_symb_state (symb_state : symbolic_state) : (symbolic_heap * predicate_set * substitution) option  = 
	let pat_heap, pat_store, pat_pf, pat_gamma, pat_preds = pat_symb_state in 
	let heap, store, pf, gamma, preds = symb_state in
	let subst = init_substitution lvars in 
	
	if (unify_stores pat_store store subst) then 
		begin 
		let quotient_heap : symbolic_heap option = unify_symb_heaps pat_heap heap pf gamma subst in 
		let new_subst, quotient_preds = unify_pred_arrays pat_preds preds pf gamma subst in 
		(match new_subst, quotient_heap with 
		| Some new_subst, Some quotient_heap ->
			Printf.printf "I computed a quotient heap but I also need to check an entailment\n"; 
			Printf.printf "the symbolic state after computing quotient heap:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state);
			(if ((check_entailment_pf pf pat_pf gamma new_subst) && (unify_gamma pat_gamma gamma new_subst)) then 
				Some (quotient_heap, quotient_preds, new_subst)
				else None)
		| _ ->  None)
		end 
		else None


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

		
			
let merge_heaps heap new_heap p_formulae gamma = 
	(** 	let str_heap = JSIL_Memory_Print.string_of_shallow_symb_heap heap in 
	Printf.printf "heap 1: %s\n" str_heap; 			
				*)
	LHeap.iter 
		(fun loc (n_fv_list, n_def) ->
			match n_def with 
			| LUnknown ->  
				(try
					begin  
					let fv_list, def = LHeap.find heap loc in 
					let rec loop q_fv_list n_fv_list = 
						(match n_fv_list with 
						| [] -> q_fv_list 
						| (le_field, le_val) :: rest_n_fv_list -> 
							(* Printf.printf "le_field: %s, le_val: %s\n" (JSIL_Print.string_of_logic_expression le_field false) (JSIL_Print.string_of_logic_expression le_val false); *)
							let _, fv_pair = find_field fv_list le_field p_formulae gamma in 
							(match fv_pair with 
							| None -> loop ((le_field, le_val) :: q_fv_list) rest_n_fv_list 
							| Some _ -> raise (Failure "heaps non-mergeable"))) in 
					let q_fv_list = loop [] n_fv_list in 
					LHeap.replace heap loc (q_fv_list @ fv_list, def)
					end
				with _ -> LHeap.add heap loc (n_fv_list, LUnknown))
			| _ -> raise (Failure "heaps non-mergeable"))
		new_heap
		

let merge_gammas gamma_l gamma_r = 
	Hashtbl.iter 
		(fun var v_type -> 
			try 
				Hashtbl.find gamma_l var; ()  
			with _ -> 
				Hashtbl.add gamma_l var v_type)
		gamma_r


let merge_symb_states symb_state_l symb_state_r subst = 
	let heap_l, store_l, pf_l, gamma_l, preds_l = symb_state_l in 
	let heap_r, store_r, pf_r, gamma_r, preds_r = symb_state_r in 
	let s_heap_r = heap_substitution heap_r subst in   
	let s_pf_r = pf_substitution pf_r subst in 
		Printf.printf("Done with pf substitution\n"); 
	let s_gamma_r = gamma_substitution gamma_r subst in 
	let s_preds_r = preds_substitution preds_r subst in 
	merge_heaps heap_l s_heap_r pf_l gamma_l;
	DynArray.append pf_l pf_r;
	merge_gammas gamma_l s_gamma_r;  
	DynArray.append preds_l s_preds_r


let symb_evaluate_bcmd bcmd symb_state = 
	let heap, store, pure_formulae, gamma, _ = symb_state in 
	match bcmd with 
	| SSkip -> LLit Empty

	| SAssignment (x, e) -> 
		let nle, t_le, _ = safe_symb_evaluate_expr e store gamma in 
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
		let ne1, t_le1, _ = safe_symb_evaluate_expr e1 store gamma in
		let ne2, t_le2, _ = safe_symb_evaluate_expr e2 store gamma in 	
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
		let ne1, t_le1, _ = safe_symb_evaluate_expr e1 store gamma in
		let ne2, t_le2, _ = safe_symb_evaluate_expr e2 store gamma in 	
		let ne3, _, _ = safe_symb_evaluate_expr e3 store gamma in
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
		let ne1, t_le1, _ = safe_symb_evaluate_expr e1 store gamma in
		let ne2, t_le2, _ = safe_symb_evaluate_expr e2 store gamma in
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
		let ne1, t_le1, _ = safe_symb_evaluate_expr e1 store gamma in
		let ne2, t_le2, _ = safe_symb_evaluate_expr e2 store gamma in
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


let find_and_apply_spec prog proc_name proc_specs symb_state = 
	let proc = try Hashtbl.find prog proc_name with
		| _ -> raise (Failure (Printf.sprintf "The procedure %s you're trying to call doesn't exist. Ew." proc_name)) in
	
	let rec find_correct_spec spec_list = 
		(match spec_list with 
		| [] -> None 
		| spec :: rest_spec_list -> 
		
			let unifier = unify_symb_states [] spec.n_pre symb_state in 
			(match unifier with 
			| Some (quotient_heap, quotient_preds, subst) ->	
				let _, store, p_formulae, gamma, preds = symb_state in 
				let new_symb_state = (quotient_heap, store, p_formulae, gamma, preds) in
				Printf.printf "I found a precondition that is applicable!\n"; 
				merge_symb_states new_symb_state spec.n_post subst; 
				Printf.printf "I merged the symbolic states!\n";
				let ret_flag = spec.n_ret_flag in 
				
				let ret_lexpr = 
					(match ret_flag with 
					| Normal ->  
						let ret_var = proc.ret_var in 
						(match ret_var with 
						| None -> None 
						| Some ret_var ->  
							try 
								let ret_lexpr = Hashtbl.find (get_store spec.n_post) ret_var in 
								Some (lexpr_substitution ret_lexpr subst true)
							with _ -> None)
					
					| Error -> 
						let error_var = proc.error_var in 
						(match error_var with 
						| None -> None 
						| Some error_var ->
							try 
								let error_lexpr = Hashtbl.find (get_store spec.n_post) error_var in 
								Some (lexpr_substitution error_lexpr subst true)
							with _ -> None)) in   	
				Some (new_symb_state, ret_flag, ret_lexpr)
				
			| None -> (find_correct_spec rest_spec_list))) in 
	find_correct_spec (proc_specs.n_proc_specs)


let rec symb_evaluate_cmd symb_prog cur_proc_name spec vis_tbl cur_symb_state cur_cmd prev_cmd = 	
	
	let f_state_change = symb_evaluate_cmd symb_prog cur_proc_name spec vis_tbl in 
	let f = f_state_change cur_symb_state in 
	
	let proc = try Hashtbl.find symb_prog.program cur_proc_name with
		| _ -> raise (Failure (Printf.sprintf "The procedure %s you're trying to call doesn't exist. Ew." cur_proc_name)) in  
	
	let f_next_state_change = symb_evaluate_next_command symb_prog proc spec vis_tbl in
	let f_next = f_next_state_change cur_symb_state in
	
	let keep_on_searching i = 
		try 
			let _ = Hashtbl.find vis_tbl i in 
			let i_metadata, _ = proc.proc_body.(i) in 
			(match (i_metadata.pre_cond) with 
			| None -> raise (Failure "back edges need to point to commands annotated with invariants")
			| Some _ -> false)
		with _ -> true in  		
	
	let f_jump_next next_cmd cur_cmd copy_state branch_expr =
		let new_pfs = (match branch_expr with 
		| None -> []
		| Some (ve, negate_ve) -> 
			let _, a_ve = lift_logic_expr ve in 
			(match a_ve with 
			| None -> []
			| Some a_ve ->  if (negate_ve) then [ (LNot a_ve) ] else [ a_ve ])) in 
		
		if (keep_on_searching next_cmd) then
			(if (copy_state) then
					let cur_symb_state = copy_symb_state cur_symb_state in
					extend_symb_state_with_pfs cur_symb_state new_pfs; 
					f_state_change cur_symb_state next_cmd cur_cmd
				else 
					extend_symb_state_with_pfs cur_symb_state new_pfs; 
					f_state_change cur_symb_state next_cmd cur_cmd)
			else () in 
		
	let cmd = proc.proc_body.(cur_cmd) in 
	
	Hashtbl.replace vis_tbl cur_cmd true; 
	let metadata, cmd = cmd in
	match cmd with 
	| SBasic bcmd -> 
		let _ = symb_evaluate_bcmd bcmd cur_symb_state in  
		(f_next cur_cmd prev_cmd)
		 
	| SGoto i -> f i cur_cmd 
	
	| SGuardedGoto (e, i, j) -> 
		let v_e = symb_evaluate_expr e (get_store cur_symb_state) (get_gamma cur_symb_state) in
		if (isEqual v_e (LLit (Bool true)) (get_pf cur_symb_state) (get_gamma cur_symb_state)) then 
			f_jump_next i cur_cmd false None
			else (if (isEqual v_e (LLit (Bool false)) (get_pf cur_symb_state) (get_gamma cur_symb_state)) then
				f_jump_next j cur_cmd false None
				else   
					f_jump_next i cur_cmd false (Some (v_e, false)); 
					f_jump_next j cur_cmd true (Some (v_e, true)))
	
	| SCall (x, e, e_args, j) ->
		(*  "symbolically executing a procedure call - ai que locura!!!\n"; *)
		let proc_name = symb_evaluate_expr e (get_store cur_symb_state) (get_gamma cur_symb_state) in
		let proc_name = 
			match proc_name with 
			| LLit (String proc_name) -> 
				if (!verbose) then Printf.printf "\nExecuting procedure %s\n" proc_name; 
				proc_name 
			| _ ->
				let msg = Printf.sprintf "Symb Execution Error - Cannot analyse a procedure call without the name of the procedure. Got: %s." (JSIL_Print.string_of_logic_expression proc_name false) in 
				raise (Failure msg) in 
	
		let proc_specs = try 
			Hashtbl.find symb_prog.spec_tbl proc_name 
		with _ ->
			let msg = Printf.sprintf "No spec found for proc %s" proc_name in 
			raise (Failure msg) in 
	
		let symb_state_str = JSIL_Memory_Print.string_of_shallow_symb_state cur_symb_state in 
		Printf.printf "About to call the procedure %s in the symbolic state:\n%s" proc_name symb_state_str; 
		(match (find_and_apply_spec symb_prog.program proc_name proc_specs cur_symb_state) with 
		| Some (symb_state, ret_flag, ret_val) -> 
			(match ret_flag with 
			| Normal -> f_next_state_change symb_state cur_cmd prev_cmd
			| Error ->
				(match j with 
				| None -> 
					let msg = Printf.sprintf "Procedure %s may return an error, but no error label was provided." proc_name in 
					raise (Failure msg)
				| Some j -> 
					if (keep_on_searching j) then 
						f_state_change symb_state j cur_cmd
					else ()))
		| None -> 
			
			let msg = Printf.sprintf "No precondition of procedure %s matches the current symbolic state" proc_name in 
			raise (Failure msg))
	
	| _ -> raise (Failure "not implemented yet")
and 
symb_evaluate_next_command s_prog proc spec vis_tbl cur_symb_state cur_cmd prev_cmd =
	let cur_proc_name = proc.proc_name in 
	if (Some cur_cmd = proc.ret_label) then 
		check_final_symb_state cur_proc_name spec cur_symb_state Normal
	else (if (Some cur_cmd = proc.error_label) then 
		check_final_symb_state cur_proc_name spec cur_symb_state Error 
	else
		let next_cmd = 
			(if ((cur_cmd + 1) < (Array.length proc.proc_body)) then 
				Some proc.proc_body.(cur_cmd + 1) 
			else None) in 
		let next_prev = 
			match next_cmd with 
			| Some (_, SPsiAssignment (_, _)) -> prev_cmd 
			| _ -> cur_cmd in 
		symb_evaluate_cmd s_prog cur_proc_name spec vis_tbl cur_symb_state (cur_cmd + 1) next_prev)
and 
check_final_symb_state proc_name spec symb_state flag = 
	let print_error_to_console msg = 
		(if (msg = "") 
			then Printf.printf "Failed to verify a spec of proc %s\n" proc_name
			else Printf.printf "Failed to verify a spec of proc %s -- %s\n" proc_name msg); 
		let final_symb_state_str = JSIL_Memory_Print.string_of_shallow_symb_state symb_state in 
		let post_symb_state_str = JSIL_Memory_Print.string_of_shallow_symb_state spec.n_post in
		Printf.printf "Final symbolic state: %s\n" final_symb_state_str;
		Printf.printf "Post condition: %s\n" post_symb_state_str in 
	
	Printf.printf "the symbolic state before unification:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state);
	let unifier = unify_symb_states spec.n_lvars spec.n_post symb_state in 
	match unifier with 
	| Some (quotient_heap, quotient_preds, _) ->	
		if ((is_symb_heap_empty quotient_heap) && (is_preds_empty quotient_preds))
			then Printf.printf "Verified one spec of proc %s\n" proc_name
			else (print_error_to_console "incomplete match"; raise (Failure "post condition is not unifiable"))
	| None -> (print_error_to_console "non_unifiable heaps";  raise (Failure "post condition is not unifiable"))


let symb_evaluate_proc s_prog proc_name spec = 
	let vis_tbl = Hashtbl.create 31 in 
	symb_evaluate_cmd s_prog proc_name spec vis_tbl spec.n_pre 0 0


let sym_run_procs spec_table prog which_pred = 
	let s_prog = {
		program = prog; 
		which_pred = which_pred; 
		spec_tbl = spec_table
	} in 
	let results = Hashtbl.fold 
		(fun proc_name spec ac_results ->
			let pre_post_list = spec.n_proc_specs in 
			let results = List.map  
				(fun pre_post ->
					(try
						symb_evaluate_proc s_prog proc_name pre_post;
						(proc_name, pre_post, true, None)
					 with Failure msg ->
						(proc_name, pre_post, false, Some msg)
					))
				pre_post_list in
			ac_results @ results)
		spec_table
		[] in 
	let results_str = JSIL_Memory_Print.string_of_symb_exe_results results in 
	results_str
	
	
	