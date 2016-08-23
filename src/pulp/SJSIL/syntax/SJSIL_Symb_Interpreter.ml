open SSyntax
open Entailment_Engine

let verbose = ref false

let proto_f = "@proto"

let rec lexpr_substitution lexpr subst = 
	let f e = lexpr_substitution e subst in 
	match lexpr with 
	| LLit lit -> LLit lit 
	| LNone -> LNone
	
	| LVar var -> (try Hashtbl.find subst var with _ -> LVar (JSIL_Logic_Normalise.fresh_lvar ()))
	
	| ALoc aloc -> (try Hashtbl.find subst aloc with _ -> ALoc (JSIL_Logic_Normalise.fresh_aloc ())) 
								
	| PVar _ -> raise (Failure "Illegal program variable in logical expression. lexpr_substitution requires its argument to be normalized.")

	| LBinOp (le1, op, le2) -> LBinOp ((f le1), op, (f le2)) 
	
	| LUnOp (op, le) -> LUnOp (op, (f le)) 
	
	| LEVRef (le1, le2) -> LEVRef ((f le1), (f le2))
	
	| LEORef (le1, le2) -> LEORef ((f le1), (f le2))
	
	| LBase le -> LBase	(f le)

	| LField le -> LField (f le)

	| LTypeOf le -> LTypeOf (f le) 
	
	| LCons (le1, le2) -> LCons ((f le1), (f le2))
	
	| LEList les -> 
		let s_les = List.map (fun le -> (f le)) les in 
		LEList s_les 
	
	| LSNth (le1, le2) -> LSNth ((f le1), (f le2))
	
	| LLNth (le1, le2) -> LLNth ((f le1), (f le2))
	
	| LUnknown -> LUnknown 


let rec assertion_substitution a subst = 
	let fa a = assertion_substitution a subst in 
	let fe e = lexpr_substitution e subst in 
	match a with 
	| LAnd (a1, a2) -> LAnd ((fa a1), (fa a2)) 
	| LOr (a1, a2) -> LOr ((fa a1), (fa a2)) 
	| LNot a -> LNot (fa a) 
	| LTrue -> LTrue 
	| LFalse -> LFalse
	| LEq (e1, e2) -> LEq ((fe e1), (fe e2))
	| LLess (e1, e2) -> LLess ((fe e1), (fe e2))
	| LLessEq (e1, e2) -> LLessEq ((fe e1), (fe e2))
	| LStrLess (e1, e2) -> LStrLess ((fe e1), (fe e2)) 
	| LStar (a1, a2) -> LStar ((fa a1), (fa a2))
	| LPointsTo (e1, e2, e3) -> LPointsTo ((fe e1), (fe e2), (fe e3))
	| LEmp -> LEmp 
	| LPred (_, _) 
	| LTypeEnv _ -> raise (Failure "Substitution for assertions not defined for cases LPred and LTypeEnv")


let rec safe_symb_evaluate_expr (expr : jsil_expr) store gamma = 
	let nle = symb_evaluate_expr expr store gamma in 
	let _, is_typable = JSIL_Logic_Normalise.normalised_is_typable gamma nle in 
	if (is_typable) 
		then nle 
		else 
			begin 
				let gamma_str = JSIL_Logic_Print.string_of_gamma gamma in 
				let msg = Printf.sprintf "The logical expression %s is not typable in the typing enviroment: %s" (JSIL_Logic_Print.string_of_logic_expression nle false) gamma_str in
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
		let nle1 = safe_symb_evaluate_expr e1 store gamma in 
		let nle2 = safe_symb_evaluate_expr e2 store gamma in 
		(match nle1, nle2 with
		| LLit l1, LLit l2 -> 
			let l = SJSIL_Interpreter.evaluate_binop op l1 l2 in 
			LLit l
		| _, _ -> LBinOp (nle1, op, nle2))
	
	| UnaryOp (op, e) -> 
		let nle = safe_symb_evaluate_expr e store gamma in
		(match nle with 
		| LLit lit -> LLit (SJSIL_Interpreter.evaluate_unop op lit)
		| _ -> LUnOp (op, nle))
	
	| VRef (e1, e2) ->
		let nle1 = safe_symb_evaluate_expr e1 store gamma in 
		let nle2 = safe_symb_evaluate_expr e2 store gamma in 
		(match nle1, nle2 with 
		| LLit l, LLit (String field) -> LLit (LVRef (l, field))
		| _, _ -> LEVRef (nle1, nle2))
	
	| ORef (e1, e2) ->
		let nle1 = safe_symb_evaluate_expr e1 store gamma in 
		let nle2 = safe_symb_evaluate_expr e2 store gamma in 
		(match nle1, nle2 with 
		| LLit l, LLit (String field) -> LLit (LORef (l, field))
		| _, _ -> LEORef (nle1, nle2))
	
	| Base	(e) -> 
		let nle = safe_symb_evaluate_expr e store gamma in 
		(match nle with 
		| LLit (LVRef (l, _)) 
		| LLit (LORef (l, _)) -> LLit l
		| LEVRef (eb, _) 
		| LEORef (eb, _) -> eb
		| _ -> LBase (nle))
	
	| Field	(e) -> 
		let nle = safe_symb_evaluate_expr e store gamma in 
		(match nle with 
		| LLit (LVRef (_, f)) 
		| LLit (LORef (_, f)) -> LLit (String f)
		| LEVRef (_, fe) 
		| LEORef (_, fe) -> fe
		| _ -> LField (nle))	
	
	| TypeOf (e) -> 
		let nle = safe_symb_evaluate_expr e store gamma in 
		(match nle with 
		| LLit llit -> LLit (Type (SJSIL_Interpreter.evaluate_type_of llit)) 
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
	
	| LNth (e1, e2) ->
		let list = safe_symb_evaluate_expr e1 store gamma in
		let index = safe_symb_evaluate_expr e2 store gamma in
		(match list, index with 
		| LLit (LList list), LLit (Num n) -> 
			(try (LLit (List.nth list (int_of_float n))) with _ -> 
					raise (Failure "List index out of bounds"))
		
		| LEList list, LLit (Num n) ->
			(try (List.nth list (int_of_float n)) with _ -> 
					raise (Failure "List index out of bounds"))
				
		| _, _ -> LLNth (list, index))

	| SNth (e1, e2) ->
		let str = safe_symb_evaluate_expr e1 store gamma in
		let index = safe_symb_evaluate_expr e2 store gamma  in
		(match str, index with 
		| LLit (String s), LLit (Num n) -> 
			LLit (String (String.make 1 (String.get s (int_of_float n))))
				
		| _, _ -> LSNth (str, index))
	
	| EList es ->
		let les = 
			List.map (fun e -> safe_symb_evaluate_expr e store gamma) es in 
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
	
	| Cons (e1, e2) -> 
		let value = safe_symb_evaluate_expr e1 store gamma in
		let list = safe_symb_evaluate_expr e2 store gamma in
		(match list with 
		| LLit (LList list) ->
			(match value with 
			| LLit l -> LLit (LList (l :: list))
			| _ -> 
				let les = List.map (fun l -> LLit l) list in 
				LEList (value :: les))
		| LEList les -> LEList (value :: les)  
		| _ -> LCons (value, list))	 
	
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


let update_abs_store store x ne = 
	(* Printf.printf "I am in the update store\n"; 
	let str_store = "\t Store: " ^ (JSIL_Logic_Print.string_of_shallow_symb_store store) ^ "\n" in 
	Printf.printf "%s" str_store;  *)
	Hashtbl.replace store x ne

let isEqual e1 e2 pure_formulae = (e1 = e2) 

let isDifferent e1 e2 pure_formulae = 
	match e1, e2 with 
	| LLit l1, LLit l2 -> (not (l1 = l2)) 
	| ALoc aloc1, ALoc aloc2 -> (not (aloc1 = aloc2))
	| _, _ -> false 

(**
  find_field fv_list e p_formulae = fv_list', (e1, e2)
	   st: 
		    fv_list = fv_list' U (e1, e2)  
				and 
				pure_formulae |=
					
*)
let find_field fv_list e p_formulae = 
	let rec find_field_rec fv_list traversed_fv_list = 
		match fv_list with 
		| [] -> traversed_fv_list, None 
		| (e_field, e_value) :: rest ->
			(if (isEqual e e_field p_formulae)
				then traversed_fv_list @ rest, Some (e_field, e_value)
				else 
					(if (isDifferent e e_field p_formulae)
						then find_field_rec rest ((e_field, e_value) :: traversed_fv_list)
						else 
							let e_str = JSIL_Logic_Print.string_of_logic_expression e false  in  
							let msg = Printf.sprintf "I cannot decide whether or not the field denoted by %s already exists in the symbolic heap" e_str in   
							raise (Failure msg))) in 
	find_field_rec fv_list []


let update_abs_heap_default (heap : symbolic_heap) loc e =
	let fv_list, default_val = try LHeap.find heap loc with _ -> [], LUnknown in 
	match default_val with 
	| LUnknown -> LHeap.replace heap loc (fv_list, e)    
 	| _ -> raise (Failure "the default value for the fields of a given object cannot be changed once set") 


let update_abs_heap (heap : symbolic_heap) loc e_field e_val p_formulae =
	(* Printf.printf "Update Abstract Heap\n"; *)
	let fv_list, default_val = try LHeap.find heap loc with _ -> [], LUnknown in 
	let unchanged_fv_list, _ = find_field fv_list e_field p_formulae in 
	LHeap.replace heap loc ((e_field, e_val) :: unchanged_fv_list, default_val)    


let abs_heap_find heap l e p_formulae = 
	let fv_list, default_val = try LHeap.find heap l with _ -> [], LUnknown in 
	let _, field_val_pair = find_field fv_list e p_formulae in
	match field_val_pair with 
	| Some (_, f_val) -> f_val
	| None -> default_val

let abs_heap_delete heap l e p_formulae = 
	let fv_list, default_val = try LHeap.find heap l with _ -> [], LUnknown in 
	let rest_fv_pairs, del_fv_pair = find_field fv_list e p_formulae in
	match del_fv_pair with 
	| Some (_, _) -> LHeap.replace heap l (rest_fv_pairs, default_val) 
	| None -> raise (Failure "Trying to delete an inexistent field") 
		
		
let unify_stores (pat_store : symbolic_store) (store : symbolic_store) :  (string, jsil_logic_expr) Hashtbl.t option = 
	let subst = Hashtbl.create 31 in
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
		Some subst
	with _ -> None


let unify_lexprs le_pat (le : SSyntax.jsil_logic_expr) p_formulae (subst : (string, SSyntax.jsil_logic_expr) Hashtbl.t) : (bool * ((string * jsil_logic_expr) option)) = 
	match le_pat with 
	| LVar var 
	| ALoc var ->  
		(try 
			if (isEqual (Hashtbl.find subst var) le p_formulae)
				then (true, None)
				else (false, None)	
		with _ ->	(true, Some (var, le))) 
			
	| LLit lit -> 
		if (isEqual le_pat le p_formulae) 
			then (true, None)
			else (false, None)
	
	| _ -> raise (Failure "Illegal expression in pattern to unify")

let update_subst1 subst unifier = 
	match unifier with 
	| false, _ -> false
	| _, Some (var, le) -> Hashtbl.add subst var le; true 
	| _, None -> true

let update_subst2 subst unifier1 unifier2 p_formulae = 
	match unifier1, unifier2 with 
	| (true, None), (true, None) -> true

	| (true, Some _), (true, None) -> update_subst1 subst unifier1
	
	| (true, None), (true, Some _) -> update_subst1 subst unifier2

	| (true, Some (var1, le1)), (true, Some (var2, le2)) -> 
		if (var1 = var2) 
			then 
				begin 
					if (isEqual le1 le2 p_formulae) 
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


let unify_fv_pair (pat_field, pat_value) (fv_list : (jsil_logic_expr * jsil_logic_expr) list) p_formulae subst :  (jsil_logic_expr * jsil_logic_expr) list option = 
	let rec loop fv_list traversed_fv_list = 
		match fv_list with 
		| [] -> None
		| (e_field, e_value) :: rest ->
			let field_unifier = unify_lexprs pat_field e_field p_formulae subst in 
			let value_unifier = unify_lexprs pat_value e_value p_formulae subst in 
			if (update_subst2 subst field_unifier value_unifier p_formulae) 
				then 
					Some (traversed_fv_list @ rest)
				else
					loop rest ((e_field, e_value) :: traversed_fv_list) in
	loop fv_list []


let unify_symb_fv_lists pat_fv_list fv_list def_val p_formulae subst : (jsil_logic_expr * jsil_logic_expr) list option = 
	(** 
		let error_msg pat_field pat_val = 
		let pat_field_str = JSIL_Logic_Print.string_of_logic_expression pat_field false in 
		let pat_val_str = JSIL_Logic_Print.string_of_logic_expression pat_val false in 
			Printf.sprintf "Field-val pair (%s, %s) in pattern has not been matched" pat_field_str pat_val_str in
	*)
	let rec loop (fv_list : (jsil_logic_expr * jsil_logic_expr) list) (pat_list : (jsil_logic_expr * jsil_logic_expr) list) = 
		match pat_list with 
		| [] -> Some fv_list 
		| (pat_field, pat_val) :: rest_pat_list -> 
			let rest_fv_list = unify_fv_pair (pat_field, pat_val) fv_list p_formulae subst in 
			(match rest_fv_list with
			| None -> 
				(match def_val with 
				| LUnknown -> None
				| _ ->
					let unifier = unify_lexprs pat_val def_val p_formulae subst in 
					if (update_subst1 subst unifier) 
						then loop fv_list rest_pat_list
						else None)
			| Some rest_fv_list -> loop rest_fv_list rest_pat_list) in  
	loop fv_list pat_fv_list
		
		
let unify_symb_heaps (pat_heap : symbolic_heap) (heap : symbolic_heap) pure_formulae (subst : (string, jsil_logic_expr) Hashtbl.t) : symbolic_heap option = 
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
					let fv_list, def = 
						(try LHeap.find heap loc with _ -> 
							let msg = Printf.sprintf "Location %s in pattern has not been matched" loc in 
							raise (Failure msg)) in 
						let new_fv_list = unify_symb_fv_lists pat_fv_list fv_list def pure_formulae subst in
						(match new_fv_list with 
						| Some new_fv_list -> LHeap.replace quotient_heap loc (new_fv_list, def)
						| None -> raise (Failure ("Pattern heaps cannot have default values")))
				| _ -> raise (Failure ("Pattern heaps cannot have default values"))))
			pat_heap;  
		Some quotient_heap
	with _ -> None
	
let check_entailment_pf pf pat_pf gamma subst = 
	Printf.printf "I am inside the check entailment patati patata\n";
	let pf_list = DynArray.to_list pf in 
	let pat_pf_list = 
		(List.map 
			(fun a -> assertion_substitution a subst) 
			(DynArray.to_list pat_pf)) in 
	Entailment_Engine.check_entailment pf_list pat_pf_list gamma
		
						
let unify_symb_heaps_top_level pat_heap pat_store (pat_pf : jsil_logic_assertion DynArray.t) pat_gamma heap store pf gamma : (symbolic_heap * ((string, jsil_logic_expr) Hashtbl.t)) option  = 
	let subst = unify_stores pat_store store in 
	(match subst with 
	| None -> None 
	| Some subst -> 
		let quotient_heap : symbolic_heap option = unify_symb_heaps pat_heap heap pf subst in 
		(match quotient_heap with 
		| None -> None
		| Some quotient_heap ->
			if (check_entailment_pf pf pat_pf gamma subst) then 
				Some (quotient_heap, subst)
				else None))

let is_symb_heap_empty heap = 
	LHeap.fold  
		(fun loc (fv_list, def) ac -> 
			match fv_list with 
			| [] -> ac 
			| _ -> false)
		heap 
		true

let fv_list_substitution fv_list subst = 
	List.map 
		(fun (le_field, le_val) -> 
			let s_le_field = lexpr_substitution le_field subst in 
			let s_le_val = lexpr_substitution le_val subst in 
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
			let s_def = lexpr_substitution def subst in
			LHeap.add new_heap s_loc (s_fv_list, s_def))
		heap; 
	new_heap
			
			
let merge_heaps heap new_heap p_formulae = 
	(** 	let str_heap = JSIL_Logic_Print.string_of_shallow_symb_heap heap in 
	Printf.printf "heap 1: %s\n" str_heap; 			
				
	let str_new_heap = JSIL_Logic_Print.string_of_shallow_symb_heap new_heap in 
	Printf.printf "new_heap 1: %s\n" str_new_heap; *)
	
	LHeap.iter 
		(fun loc (n_fv_list, n_def) ->
			match n_def with 
			| LUnknown ->  
				try
					begin  
					let fv_list, def = LHeap.find heap loc in 
					let rec loop q_fv_list n_fv_list = 
						(match n_fv_list with 
						| [] -> q_fv_list 
						| (le_field, le_val) :: rest_n_fv_list -> 
							(* Printf.printf "le_field: %s, le_val: %s\n" (JSIL_Logic_Print.string_of_logic_expression le_field false) (JSIL_Logic_Print.string_of_logic_expression le_val false); *)
							let _, fv_pair = find_field fv_list le_field p_formulae in 
							(match fv_pair with 
							| None -> loop ((le_field, le_val) :: q_fv_list) rest_n_fv_list 
							| Some _ -> raise (Failure "heaps non-mergeable"))) in 
					let q_fv_list = loop [] n_fv_list in 
					LHeap.replace heap loc (q_fv_list @ fv_list, def)
					end
				with _ -> LHeap.add heap loc (n_fv_list, LUnknown)
			| _ -> raise (Failure "heaps non-mergeable"))
		new_heap


let symb_evaluate_bcmd (bcmd : basic_jsil_cmd) heap store pure_formulae gamma = 
	match bcmd with 
	| SSkip -> LLit Empty

	| SAssignment (x, e) -> 
		let nle = symb_evaluate_expr e store gamma in 
		update_abs_store store x nle; 
		nle
	
	| SNew x -> 
		let new_loc = JSIL_Logic_Normalise.fresh_aloc () in 
		update_abs_heap_default heap new_loc LNone;
		update_abs_heap heap new_loc (LLit (String proto_f)) (LLit Null) pure_formulae; 
		update_abs_store store x (ALoc new_loc); 
		ALoc new_loc 
	
	| SMutation (e1, e2, e3) ->
		let ne1 = symb_evaluate_expr e1 store gamma in
		let ne2 = symb_evaluate_expr e2 store gamma in 	
		let ne3 = symb_evaluate_expr e3 store gamma in
		(match ne1 with 
		| LLit (Loc l) 
		| ALoc l -> 
			(* Printf.printf "I am going to call: Update Abstract Heap\n"; *)
			update_abs_heap heap l ne2 ne3 pure_formulae
		| _ -> 
			let ne1_str = JSIL_Logic_Print.string_of_logic_expression ne1 false  in 
			let msg = Printf.sprintf "I do not know which location %s denotes in the symbolic heap" ne1_str in 
			raise (Failure msg)); 
		ne3
	
	| SLookup (x, e1, e2) -> 
		let ne1 = symb_evaluate_expr e1 store gamma in
		let ne2 = symb_evaluate_expr e2 store gamma in 	
		let l = 
			(match ne1 with 
			| LLit (Loc l) 
			| ALoc l -> l
			| _ -> 
			let ne1_str = JSIL_Logic_Print.string_of_logic_expression ne1 false  in 
			let msg = Printf.sprintf "I do not know which location %s denotes in the symbolic heap" ne1_str in 
			raise (Failure msg)) in 
		let ne = abs_heap_find heap l ne2 pure_formulae in 
		update_abs_store store x ne; 
		ne
	
	| SDelete (e1, e2) -> 
		let ne1 = symb_evaluate_expr e1 store gamma in
		let ne2 = symb_evaluate_expr e2 store gamma in
		let l = 
			(match ne1 with 
			| LLit (Loc l) 
			| ALoc l -> l 
			| _ -> 
				let ne1_str = JSIL_Logic_Print.string_of_logic_expression ne1 false  in 
				let msg = Printf.sprintf "I do not know which location %s denotes in the symbolic heap" ne1_str in 
				raise (Failure msg)) in 
		abs_heap_delete heap l ne2 pure_formulae; 
		LLit (Bool true)  
				
	| _ -> 
		raise (Failure "not implemented yet!")


let find_and_apply_spec proc proc_specs heap store p_formulae gamma = 
	
	let rec find_correct_spec spec_list = 
		(match spec_list with 
		| [] -> None 
		| spec :: rest_spec_list -> 
			let pre_heap, pre_store, pre_p_formulae, pre_gamma = spec.n_pre in  
			let unifier = unify_symb_heaps_top_level pre_heap pre_store pre_p_formulae pre_gamma heap store p_formulae gamma in 
			(match unifier with 
			| Some (quotient_heap, subst) ->	
				let post_heap, post_store, post_p_formulae, post_gamma = spec.n_post in 
				let ret_flag = spec.n_ret_flag in 
				let s_post_heap = heap_substitution post_heap subst in 
				merge_heaps quotient_heap s_post_heap p_formulae;
				let ret_lexpr = 
					(match ret_flag with 
					| Normal ->  
						let ret_var = proc.ret_var in 
						(match ret_var with 
						| None -> None 
						| Some ret_var ->  
							try 
								let ret_lexpr = Hashtbl.find post_store ret_var in 
								Some (lexpr_substitution ret_lexpr subst)
							with _ -> None)
					
					| Error -> 
						let error_var = proc.error_var in 
						(match error_var with 
						| None -> None 
						| Some error_var ->
							try 
								let error_lexpr = Hashtbl.find post_store error_var in 
								Some (lexpr_substitution error_lexpr subst)
							with _ -> None)) in 
				
				Some (quotient_heap, store, p_formulae, gamma, ret_flag, ret_lexpr)
				
			| None -> (find_correct_spec rest_spec_list))) in 
	find_correct_spec (proc_specs.n_proc_specs)


let rec symb_evaluate_cmd (spec_table : (string, SSyntax.jsil_n_spec) Hashtbl.t) post ret_flag prog cur_proc_name which_pred heap store pure_formulae gamma cur_cmd prev_cmd = 	
	let f = symb_evaluate_cmd spec_table post ret_flag prog cur_proc_name which_pred heap store pure_formulae gamma in 
	
	let proc = try SProgram.find prog cur_proc_name with
		| _ -> raise (Failure (Printf.sprintf "The procedure %s you're trying to call doesn't exist. Ew." cur_proc_name)) in  
	let cmd = proc.proc_body.(cur_cmd) in 
	let cmd_str = SSyntax_Print.string_of_cmd cmd 0 0 false false false in 
	(* Printf.printf ("cmd: %s \n") cmd_str;
	let str_store = "\t Store: " ^ (JSIL_Logic_Print.string_of_shallow_symb_store store) ^ "\n" in 
	Printf.printf "%s" str_store; *) 
	let metadata, cmd = cmd in
	match cmd with 
	| SBasic bcmd -> 
		let _ = symb_evaluate_bcmd bcmd heap store pure_formulae gamma in 
	  symb_evaluate_next_command spec_table post ret_flag prog proc which_pred heap store pure_formulae gamma cur_cmd prev_cmd
		 
	| SGoto i -> f i cur_cmd 
	
	| SGuardedGoto (e, i, j) -> 
		let v_e = symb_evaluate_expr e store gamma in
		(match v_e with 
		| LLit (Bool true) -> f i cur_cmd 
		| LLit (Bool false) -> f j cur_cmd 
		| _ -> 
			let copy_heap = LHeap.copy heap in 
			symb_evaluate_cmd spec_table post ret_flag prog cur_proc_name which_pred heap store pure_formulae gamma i cur_cmd; 
			symb_evaluate_cmd spec_table post ret_flag prog cur_proc_name which_pred copy_heap store pure_formulae gamma j cur_cmd)
	
	| SCall (x, e, e_args, j) ->
		(* Printf.printf "symbolically executing a procedure call - ai que locura!!!\n"; *)
		let proc_name = symb_evaluate_expr e store gamma in
		let proc_name = 
			match proc_name with 
			| LLit (String proc_name) -> 
				if (!verbose) then Printf.printf "\nExecuting procedure %s\n" proc_name; 
				proc_name 
			| _ ->
				let msg = Printf.sprintf "Symb Execution Error - Cannot analyse a procedure call without the name of the procedure. Got: %s." (JSIL_Logic_Print.string_of_logic_expression proc_name false) in 
				raise (Failure msg) in 
		let v_args = List.map (fun e -> symb_evaluate_expr e store gamma) e_args in 
		let proc_specs = try 
			Hashtbl.find spec_table proc_name 
		with _ ->
			let msg = Printf.sprintf "No spec found for proc %s" proc_name in 
			raise (Failure msg) in 
		(match (find_and_apply_spec proc proc_specs heap store pure_formulae gamma) with 
		| Some (heap, store, pure_formulae, gamma, ret_flag, ret_val) -> 
			(match ret_flag with 
			| Normal -> 
				(** let str_heap = JSIL_Logic_Print.string_of_shallow_symb_heap heap in 
				Printf.printf "Heap after calling the procedure:\n%s\n" str_heap; *)
				symb_evaluate_next_command spec_table post ret_flag prog proc which_pred heap store pure_formulae gamma cur_cmd prev_cmd
			| Error ->
				(match j with 
				| None -> 
					let msg = Printf.sprintf "Procedure %s returned an error, but no error label was provided." proc_name in 
					raise (Failure msg)
				| Some j -> 
					symb_evaluate_cmd spec_table post ret_flag prog cur_proc_name which_pred heap store pure_formulae gamma j cur_cmd))
		| None -> 
			let msg = Printf.sprintf "No precondition of procedure %s matches the current symbolic state" proc_name in 
			raise (Failure msg))
	
	| _ -> raise (Failure "not implemented yet")
and 
symb_evaluate_next_command spec_table post ret_flag prog proc which_pred heap store pure_formulae gamma cur_cmd prev_cmd =
	let cur_proc_name = proc.proc_name in 
	if (Some cur_cmd = proc.ret_label)
	then 
		(let ret_var = 
			(match proc.ret_var with
			| None -> raise (Failure "No no!") 
			| Some ret_var -> ret_var) in 
		let ret_expr = (try (Hashtbl.find store ret_var) with
			| _ -> 
				let str_store = "\t Store: " ^ (JSIL_Logic_Print.string_of_shallow_symb_store store) ^ "\n" in 
				Printf.printf "%s" str_store; 
				raise (Failure (Printf.sprintf "Cannot find return variable."))) in 
		check_final_symb_state cur_proc_name post ret_flag heap store gamma Normal ret_expr pure_formulae)
	else (if (Some cur_cmd = proc.error_label) 
			then 
				(let err_expr = 
					(let err_var = (match proc.error_var with 
					                      | None -> raise (Failure "No no!") 
																| Some err_var -> err_var) in
				         (try (Hashtbl.find store err_var) with
				| _ -> raise (Failure (Printf.sprintf "Cannot find error variable in proc %s, err_lab = %d, err_var = %s, cmd = %s" proc.proc_name cur_cmd err_var (SSyntax_Print.string_of_cmd proc.proc_body.(prev_cmd)  0 0 false false false))))) in
			check_final_symb_state cur_proc_name post ret_flag heap store gamma Error err_expr pure_formulae)
	else (
			let next_cmd = 
				(if ((cur_cmd + 1) < (Array.length proc.proc_body)) 
					then Some proc.proc_body.(cur_cmd+1)
					else None) in 
			let next_prev = 
				match next_cmd with 
				| Some (_, SPsiAssignment (_, _)) -> prev_cmd 
				| _ -> cur_cmd in 
			symb_evaluate_cmd spec_table post ret_flag prog cur_proc_name which_pred heap store pure_formulae gamma (cur_cmd + 1) next_prev))
and 
check_final_symb_state proc_name post ret_flag heap store gamma flag lexpr pure_formulae = 
	let post_heap, post_store, post_p_formulae, post_gamma = post in 
	let str = JSIL_Logic_Print.string_of_shallow_symb_state heap store pure_formulae gamma in 
	Printf.printf "Final symbolic state: \n %s" str; 
	
	let print_error_to_console msg = 
		(if (msg = "") 
			then Printf.printf "Failed to verify a spec of proc %s\n" proc_name
			else Printf.printf "Failed to verify a spec of proc %s -- %s\n" proc_name msg); 
		let final_symb_state_str = JSIL_Logic_Print.string_of_shallow_symb_state heap store pure_formulae gamma in 
		let post_symb_state_str = JSIL_Logic_Print.string_of_shallow_symb_state post_heap post_store post_p_formulae post_gamma in
		Printf.printf "Final symbolic state: %s\n" final_symb_state_str;
		Printf.printf "Post condition: %s\n" post_symb_state_str in 
	
	
	let unifier = unify_symb_heaps_top_level post_heap post_store post_p_formulae post_gamma heap store pure_formulae gamma in 
	
	Printf.printf "I computed the unifier\n";
	
	match unifier with 
	| Some (quotient_heap, _) ->	
		if (is_symb_heap_empty quotient_heap) 
			then Printf.printf "Verified one spec of proc %s\n" proc_name
			else (print_error_to_console "incomplete match"; raise (Failure "post condition is not unifiable"))
	| None -> (print_error_to_console "non_unifiable heaps";  raise (Failure "post condition is not unifiable"))
	