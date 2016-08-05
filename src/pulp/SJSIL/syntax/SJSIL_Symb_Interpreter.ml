open SSyntax

let verbose = ref false

let proto_f = "@proto"

let rec symb_evaluate_expr (expr : jsil_expr) store = 
	match expr with 
	| Literal lit -> LLit lit
	
	| Var var -> 
		(try Hashtbl.find store var 
		with _ -> 
			let msg = Printf.sprintf "Variable %s not found in logical store." var in 
			raise (Failure msg))
	
	| BinOp (e1, op, e2) ->
		let ne1 = symb_evaluate_expr e1 store in 
		let ne2 = symb_evaluate_expr e2 store in 
		(match ne1, ne2 with
		| LLit l1, LLit l2 -> 
			let l = SJSIL_Interpreter.evaluate_binop op l1 l2 in 
			LLit l
		| _, _ -> LBinOp (ne1, op, ne2))
	
	| UnaryOp (op, e) -> 
		let ne = symb_evaluate_expr e store in
		(match ne with 
		| LLit lit -> LLit (SJSIL_Interpreter.evaluate_unop op lit)
		| _ -> LUnOp (op, ne))
	
	| VRef (e1, e2) ->
		let ne1 = symb_evaluate_expr e1 store in 
		let ne2 = symb_evaluate_expr e2 store in 
		(match ne1, ne2 with 
		| LLit l, LLit (String field) -> LLit (LVRef (l, field))
		| _, _ -> LEVRef (ne1, ne2))
	
	| ORef (e1, e2) ->
		let ne1 = symb_evaluate_expr e1 store in 
		let ne2 = symb_evaluate_expr e2 store in 
		(match ne1, ne2 with 
		| LLit l, LLit (String field) -> LLit (LORef (l, field))
		| _, _ -> LEORef (ne1, ne2))
	
	| Base	(e) -> 
		let ne = symb_evaluate_expr e store in 
		(match ne with 
		| LLit (LVRef (l, _)) 
		| LLit (LORef (l, _)) -> LLit l
		| LEVRef (eb, _) 
		| LEORef (eb, _) -> eb
		| _ -> LBase (ne))
	
	| Field	(e) -> 
		let ne = symb_evaluate_expr e store in 
		(match ne with 
		| LLit (LVRef (_, f)) 
		| LLit (LORef (_, f)) -> LLit (String f)
		| LEVRef (_, fe) 
		| LEORef (_, fe) -> fe
		| _ -> LField (ne))	
	
	| TypeOf (e) -> 
		let ne = symb_evaluate_expr e store in 
		(match ne with 
		| LLit llit -> LLit (Type (SJSIL_Interpreter.evaluate_type_of llit)) 
		| LNone -> raise (Failure "Illegal Logic Expression: TypeOf of None")
		| PVar _ -> raise (Failure "This should never happen: program variable in normalized expression") 
		| LVar _ 
		| ALoc _ 
		| LBinOp (_, _, _)   
		| LUnOp (_, _) -> LTypeOf (ne)
		| LEVRef (_, _) -> LLit (Type VariableReferenceType)
		| LEORef (_, _) -> LLit (Type ObjectReferenceType)
		(* this is not correct *)
		| LBase _ -> LLit (Type ObjectType)
		| LField _ -> LLit (Type StringType)
		| LTypeOf _ -> LLit (Type TypeType))
	
	| LNth (e1, e2) ->
		let list = symb_evaluate_expr e1 store in
		let index = symb_evaluate_expr e2 store in
		(match list, index with 
		| LLit (LList list), LLit (Num n) -> 
			(try (LLit (List.nth list (int_of_float n))) with _ -> 
					raise (Failure "List index out of bounds"))
		
		| LEList list, LLit (Num n) ->
			(try (List.nth list (int_of_float n)) with _ -> 
					raise (Failure "List index out of bounds"))
				
		| _, _ -> LLNth (list, index))

	| SNth (e1, e2) ->
		let str = symb_evaluate_expr e1 store in
		let index = symb_evaluate_expr e2 store in
		(match str, index with 
		| LLit (String s), LLit (Num n) -> 
			LLit (String (String.make 1 (String.get s (int_of_float n))))
				
		| _, _ -> LSNth (str, index))
	
	| EList es ->
		let les = 
			List.map (fun e -> symb_evaluate_expr e store) es in 
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
		let value = symb_evaluate_expr e1 store in
		let list = symb_evaluate_expr e2 store in
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


let update_abs_store store x ne = Hashtbl.replace store x ne

let isEqual e1 e2 pure_formulae = (e1 = e2) 

let isDifferent e1 e2 pure_formulae = 
	match e1, e2 with 
	| LLit l1, LLit l2 -> (not (l1 = l2)) 
	| ALoc v1, ALoc v2 -> (not (v1 = v2))
	| _, _ -> false 

(**
  filter_field fv_list e1 pure_formulae = fv_list', (e1', e2)
	   st: 
		    fv_list = fv_list' U (e1, e2)  
				and 
				pure_formulae |= e1 = e1'  
*)
let filter_field field_val_list e1 pure_formulae = 
	let rec filter_field_rec fv_lst processed_fv_pairs = 
		match fv_lst with 
		| [] -> field_val_list, None 
		| (e_field, e_value) :: rest ->
			(if (isEqual e1 e_field pure_formulae)
				then processed_fv_pairs @ rest, Some (e_field, e_value)
				else 
					(if (isDifferent e1 e_field pure_formulae)
						then filter_field_rec rest ((e_field, e_value) :: processed_fv_pairs)
						else 
							let e1_str = JSIL_Logic_Print.string_of_logic_expression e1 false  in  
							let msg = Printf.sprintf "I cannot decide whether the field denoted by %s already exists in the symbolic heap" e1_str in   
							raise (Failure msg))) in 
	filter_field_rec field_val_list []


let update_abs_heap_default (heap : symbolic_heap) loc e =
	let field_val_list, default_val = try LHeap.find heap loc with _ -> [], None in 
	match default_val with 
	| Some _ -> raise (Failure "the default value for the fields of a given object cannot be changed") 
	| None -> LHeap.replace heap loc (field_val_list, Some e)    


let update_abs_heap (heap : symbolic_heap) loc e1 e2 pure_formulae =
	(* Printf.printf "Update Abstract Heap\n"; *)
	let field_val_list, default_val = try LHeap.find heap loc with _ -> [], None in 
	let unchanged_field_val_list, _ = filter_field field_val_list e1 pure_formulae in 
	LHeap.replace heap loc ((e1, e2) :: unchanged_field_val_list, default_val)    


let abs_heap_find heap l ne pure_formulae = 
	let field_val_list, default_val = try LHeap.find heap l with _ -> [], None in 
	let _, field_val_pair = filter_field field_val_list ne pure_formulae in
	match field_val_pair with 
	| Some (_, f_val) -> f_val
	| None  -> 
		(match default_val with 
		| Some d_val -> d_val 
		| None -> raise (Failure "You are looking up the value of a field that does exist"))

let abs_heap_delete heap l ne pure_formulae = 
	let field_val_list, default_val = try LHeap.find heap l with _ -> [], None in 
	let rest_fv_pairs, del_fv_pair = filter_field field_val_list ne pure_formulae in
	match del_fv_pair with 
	| Some (_, _) -> LHeap.replace heap l (rest_fv_pairs, default_val) 
	| None -> raise (Failure "Trying to delete an inexistent field") 
		
let unify_stores (pattern_store : symbolic_store) (store : symbolic_store) :  (string, string) Hashtbl.t = 
	let subst = Hashtbl.create 31 in
	Hashtbl.iter 
		(fun var pat_lexpr ->
			match pat_lexpr with 
			| ALoc pat_aloc -> 
				let aloc = try 
					let lexpr = Hashtbl.find store var in 
					match lexpr with 
					| ALoc aloc -> aloc 
					| _ -> raise (Failure "the stores are not unifiable")
					with _ -> raise (Failure "the stores are not unifiable") in 
			 	Hashtbl.add subst pat_aloc aloc 
			| _ -> ())
		pattern_store; 
	subst


let unify_lexprs le_post (le_final : SSyntax.jsil_logic_expr) pure_formulae (rn_tbl : (string, string) Hashtbl.t) (lvar_constraints_tbl : (string, SSyntax.jsil_logic_expr) Hashtbl.t) : unit = 
	match le_post with 
	| LVar x -> 
		let prev_le_final = 
			(try 
				Some (Hashtbl.find lvar_constraints_tbl x)
			with _ ->  	
				Printf.printf "I am putting variable %s the logical vars table\n" x; 
				Hashtbl.add lvar_constraints_tbl x le_final; 
				None) in 
		(match prev_le_final with 
		| Some prev_le_final -> 
			if (isEqual le_final prev_le_final pure_formulae) 
				then () 
				else raise (Failure "failed to unify with postcondition - problem with logical variable")
		| None -> ())
			
	| ALoc pat_aloc ->
		let aloc = try Hashtbl.find rn_tbl pat_aloc with _ -> pat_aloc in 	
		if (ALoc aloc = le_final) 
			then () 
			else raise (Failure "could not unify with postcondition")
	
	| _ -> 
		if (le_post = le_final) 
			then () 
			else raise (Failure "could not unify with postcondition")
	

let unify_symb_fv_lists post_fv_lst final_fv_lst pure_formulae rn_tbl lvar_constraints_tbl = 
	if ((List.length post_fv_lst) = (List.length final_fv_lst)) 
	then 
		(List.iter 
			(fun (post_field, post_val) -> 
				let final_field = post_field in (* this is unsound?? *)
				let _, final_field_val_pair = filter_field final_fv_lst final_field pure_formulae in 
				(match final_field_val_pair with 
				| None -> 
					let post_field_str = JSIL_Logic_Print.string_of_logic_expression post_field false in 
					let msg : string = Printf.sprintf "Field %s in post has not been matched" post_field_str in 
					raise (Failure msg)
				| Some (final_field, final_val) -> 
					unify_lexprs post_val final_val pure_formulae rn_tbl lvar_constraints_tbl))
			post_fv_lst)
	else raise (Failure "could not unify with postcondition - length mismatch") 			 
		
		
let unify_symb_heaps (post_heap : symbolic_heap) (final_heap : symbolic_heap) pure_formulae rn_tbl = 
	let lvar_constraints_tbl = Hashtbl.create 1021 in 
	LHeap.iter 
		(fun post_loc (post_fv_list, post_def) -> 
			let final_loc = try Hashtbl.find rn_tbl post_loc with _ -> post_loc in 
			let (final_fv_list, final_def) = 
				(try LHeap.find final_heap final_loc with _ -> 
					let msg = Printf.sprintf "Location %s in post has not been matched" final_loc in 
					raise (Failure msg) ) in 
			(match post_def, final_def with 
			| None, None -> () 
			| Some post_def, Some final_def -> 
				unify_lexprs post_def final_def pure_formulae rn_tbl lvar_constraints_tbl
			| _, _ -> raise (Failure ("Default values are not unifiable"))); 
			unify_symb_fv_lists post_fv_list final_fv_list pure_formulae rn_tbl lvar_constraints_tbl)
		post_heap
		
let unify_symb_heaps_top_level post_heap post_store post_pf final_heap final_store final_pf = 
	let rn_tbl = unify_stores post_store final_store in 
	unify_symb_heaps post_heap final_heap final_pf rn_tbl

let symb_evaluate_bcmd (bcmd : basic_jsil_cmd) heap store pure_formulae = 
	match bcmd with 
	| SSkip -> LLit Empty

	| SAssignment (x, e) -> 
		let nle = symb_evaluate_expr e store in 
		update_abs_store store x nle; 
		nle
	
	| SNew x -> 
		let new_loc = JSIL_Logic_Normalise.fresh_llvar () in 
		update_abs_heap_default heap new_loc LNone;
		update_abs_heap heap new_loc (LLit (String proto_f)) (LLit Null) pure_formulae; 
		update_abs_store store x (ALoc new_loc); 
		ALoc new_loc 
	
	| SMutation (e1, e2, e3) ->
		Printf.printf "smutation\n";
		let ne1 = symb_evaluate_expr e1 store in
		let ne2 = symb_evaluate_expr e2 store in 	
		let ne3 = symb_evaluate_expr e3 store in
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
		let ne1 = symb_evaluate_expr e1 store in
		let ne2 = symb_evaluate_expr e2 store in 	
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
		let ne1 = symb_evaluate_expr e1 store in
		let ne2 = symb_evaluate_expr e2 store in
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


let find_and_apply_spec proc_specs heap store pure_formulae = 
	heap, store, pure_formulae, Normal, LLit (String "bananas")


let rec symb_evaluate_cmd (spec_table : (string, SSyntax.jsil_n_spec) Hashtbl.t) post ret_flag prog cur_proc_name which_pred heap store pure_formulae cur_cmd prev_cmd = 	
	let f = symb_evaluate_cmd spec_table post ret_flag prog cur_proc_name which_pred heap store pure_formulae in 
	
	let proc = try SProgram.find prog cur_proc_name with
		| _ -> raise (Failure (Printf.sprintf "The procedure %s you're trying to call doesn't exist. Ew." cur_proc_name)) in  
	let cmd = proc.proc_body.(cur_cmd) in 
	let cmd_str = SSyntax_Print.string_of_cmd cmd 0 0 false false false in 
	Printf.printf ("cmd: %s \n") cmd_str;
	
	let metadata, cmd = cmd in
	match cmd with 
	| SBasic bcmd -> 
		let _ = symb_evaluate_bcmd bcmd heap store pure_formulae in 
	  symb_evaluate_next_command spec_table post ret_flag prog proc which_pred heap store pure_formulae cur_cmd prev_cmd
		 
	| SGoto i -> f i cur_cmd 
	
	| SGuardedGoto (e, i, j) -> 
		let v_e = symb_evaluate_expr e store in
		(match v_e with 
		| LLit (Bool true) -> f i cur_cmd 
		| LLit (Bool false) -> f j cur_cmd 
		| _ -> 
			let copy_heap = LHeap.copy heap in 
			symb_evaluate_cmd spec_table post ret_flag prog cur_proc_name which_pred heap store pure_formulae i cur_cmd; 
			symb_evaluate_cmd spec_table post ret_flag prog cur_proc_name which_pred copy_heap store pure_formulae j cur_cmd)
	
	| SCall (x, e, e_args, j) ->
		let proc_name = symb_evaluate_expr e store in
		let proc_name = 
			match proc_name with 
			| LLit (String proc_name) -> 
				if (!verbose) then Printf.printf "\nExecuting procedure %s\n" proc_name; 
				proc_name 
			| _ ->
				let msg = Printf.sprintf "Symb Execution Error - Cannot analyse a procedure call without the name of the procedure. Got: %s." (JSIL_Logic_Print.string_of_logic_expression proc_name false) in 
				raise (Failure msg) in 
		let v_args = List.map (fun e -> symb_evaluate_expr e store) e_args in 
		let proc_specs = try 
			Hashtbl.find spec_table proc_name 
		with _ ->
			let msg = Printf.sprintf "No spec found for proc %s" proc_name in 
			raise (Failure msg) in 
		let heap, store, pure_formulae, ret_flag, ret_val = find_and_apply_spec proc_specs heap store pure_formulae in 
		match ret_flag with 
		| Normal -> 
			symb_evaluate_next_command spec_table post ret_flag prog proc which_pred heap store pure_formulae cur_cmd prev_cmd
		| Error ->
			(match j with 
			| None -> 
				let msg = Printf.sprintf "Procedure %s returned an error, but no error label was provided." proc_name in 
				raise (Failure msg)
			| Some j -> 
				symb_evaluate_cmd spec_table post ret_flag prog cur_proc_name which_pred heap store pure_formulae j cur_cmd)

	| _ -> raise (Failure "not implemented yet")
and 
symb_evaluate_next_command spec_table post ret_flag prog proc which_pred heap store pure_formulae cur_cmd prev_cmd =
	let cur_proc_name = proc.proc_name in 
	if (Some cur_cmd = proc.ret_label)
	then 
			(let ret_expr = 
				(let ret_var = (match proc.ret_var with
			    					    | None -> raise (Failure "No no!") 
												| Some ret_var -> ret_var) in
				  (try (Hashtbl.find store ret_var) with
						| _ -> raise (Failure (Printf.sprintf "Cannot find return variable.")))) in
			check_final_symb_state post ret_flag heap store Normal ret_expr pure_formulae)
	else (if (Some cur_cmd = proc.error_label) 
			then 
				(let err_expr = 
					(let err_var = (match proc.error_var with 
					                      | None -> raise (Failure "No no!") 
																| Some err_var -> err_var) in
				         (try (Hashtbl.find store err_var) with
				| _ -> raise (Failure (Printf.sprintf "Cannot find error variable in proc %s, err_lab = %d, err_var = %s, cmd = %s" proc.proc_name cur_cmd err_var (SSyntax_Print.string_of_cmd proc.proc_body.(prev_cmd)  0 0 false false false))))) in
			check_final_symb_state post ret_flag heap store Error err_expr pure_formulae)
	else (
			let next_cmd = 
				(if ((cur_cmd + 1) < (Array.length proc.proc_body)) 
					then Some proc.proc_body.(cur_cmd+1)
					else None) in 
			let next_prev = 
				match next_cmd with 
				| Some (_, SPsiAssignment (_, _)) -> prev_cmd 
				| _ -> cur_cmd in 
			symb_evaluate_cmd spec_table post ret_flag prog cur_proc_name which_pred heap store pure_formulae (cur_cmd + 1) next_prev))
and 
check_final_symb_state post ret_flag heap store flag lexpr pure_formulae = 
	let post_heap, post_store, post_p_formulae = post in 
	let str = JSIL_Logic_Print.string_of_shallow_symb_state heap store pure_formulae in 
	Printf.printf "Final symbolic state: \n %s" str; 
	unify_symb_heaps_top_level post_heap post_store post_p_formulae heap store pure_formulae 
	