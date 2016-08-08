open SSyntax 
open DynArray
open Set
open Stack

module StringSet = Set.Make( 
  struct
    let compare = Pervasives.compare
    type t = string
  end )


let fresh_sth (name : string) : (unit -> string) =
  let counter = ref 0 in
  let rec f () =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f
  

let abs_loc_prefix = "_$l_"
let lvar_prefix = "_lvar_"

let fresh_llvar = fresh_sth abs_loc_prefix 
let fresh_lvar = fresh_sth lvar_prefix 


(** 
  le -> non-normalized logical expression
	subst -> table mapping variable and logical variable
	gamma -> table mapping logical variables + variables to types 
  
	the store is assumed to contain all the program variables in le
*)
let rec normalise_lexpr store gamma subst le = 
	let f = normalise_lexpr store gamma subst in 
	match le with 
	| LLit lit -> LLit lit
	| LNone -> LNone
	| LVar lvar -> (try Hashtbl.find subst lvar with _ -> LVar lvar)
	| ALoc aloc -> raise (Failure "Unsupported expression during normalization: ALoc")
	| PVar pvar -> 
		(try Hashtbl.find store pvar with
		|  _ -> 
			let msg = Printf.sprintf "Program variable %s not found: sth went wrong" pvar in 
			raise (Failure msg))
	
	| LBinOp (le1, bop, le2) -> 
		let nle1 = f le1 in 
		let nle2 = f le2 in 
		(match nle1, nle2 with 
		| LLit lit1, LLit lit2 ->
			let lit = SJSIL_Interpreter.evaluate_binop bop lit1 lit2 in 
			LLit lit
		| _, _ -> LBinOp (nle1, bop, nle2))

	| LUnOp (uop, le1) -> 
		let nle1 = f le1 in 
		(match nle1 with 
		| LLit lit1 -> 
			let lit = SJSIL_Interpreter.evaluate_unop uop lit1 in 
			LLit lit 
		| _ -> LUnOp (uop, nle1))

	| _ -> raise (Failure "Program variable not found: sth went wrong")
		
	| LEVRef (le1, le2) ->
		let nle1 = f le1 in 
		let nle2 = f le2 in 
		(match nle1, nle2 with 
		| LLit l, LLit (String field) -> LLit (LVRef (l, field))
		| _, _ -> LEVRef (nle1, nle2))
	
	| LEORef (le1, le2) ->
		let nle1 = f le1 in 
		let nle2 = f le2 in 
		(match nle1, nle2 with 
		| LLit l, LLit (String field) -> LLit (LORef (l, field))
		| _, _ -> LEORef (nle1, nle2))
	
	| LBase	(le1) -> 
		let nle1 = f le1 in 
		(match nle1 with 
		| LLit (LVRef (l, _)) 
		| LLit (LORef (l, _)) -> LLit l
		| LEVRef (leb, _) 
		| LEORef (leb, _) -> leb
		| _ -> LBase (nle1))
	
	| LField	(le1) -> 
		let nle1 = f le1 in 
		(match nle1 with 
		| LLit (LVRef (_, f)) 
		| LLit (LORef (_, f)) -> LLit (String f)
		| LEVRef (_, fe) 
		| LEORef (_, fe) -> fe
		| _ -> LField (nle1))	
				
	| LTypeOf (le1) -> 
		let nle1 = f le1 in 
		(match nle1 with 
		| LLit llit -> LLit (Type (SJSIL_Interpreter.evaluate_type_of llit)) 
		| LNone -> raise (Failure "Illegal Logic Expression: TypeOf of None")
		| LVar lvar -> 
			(try LLit (Type (Hashtbl.find gamma lvar)) with _ -> 
				raise (Failure "Logical variables always have a type"))  
		| ALoc _ -> LLit (Type ObjectType)
		| PVar _ -> raise (Failure "This should never happen: program variable in normalized expression") 
		| LBinOp (_, _, _)   
		| LUnOp (_, _) -> LTypeOf (nle1)
		| LEVRef (_, _) -> LLit (Type VariableReferenceType)
		| LEORef (_, _) -> LLit (Type ObjectReferenceType)
		| LBase _ -> LTypeOf (nle1)
		| LField _ -> LLit (Type StringType)
		| LTypeOf _ -> LLit (Type TypeType)
		| LCons (_, _) 
		| LEList _ -> LLit (Type ListType)
	  | LLNth (list, index) ->
			(match list, index with 
			| LLit (LList list), LLit (Num n) ->
				let lit_n = (try List.nth list (int_of_float n) with _ -> 
					raise (Failure "List index out of bounds")) in
				LLit (Type (SJSIL_Interpreter.evaluate_type_of lit_n))
			| LEList list, LLit (Num n) ->
				let le_n = (try List.nth list (int_of_float n) with _ ->
					 raise (Failure "List index out of bounds")) in
				f (LTypeOf le_n)
			| _, _ -> LTypeOf (nle1))
	  | LSNth (str, index) ->
			(match str, index with 
			| LLit (String s), LLit (Num n) ->
				let _ = (try (String.get s (int_of_float n)) with _ ->
					raise (Failure "String index out of bounds")) in
				LLit (Type StringType)
			| _, _ -> LTypeOf (nle1)))
		
	| LCons (le1, le2) -> 
		let nle1 = f le1 in 
		let nle2 = f le2 in 
		(match nle1, nle2 with 
		| LLit lit, LLit (LList list) -> LLit (LList (lit :: list))
		| _, LEList list -> LEList (nle1 :: list)
		| _, LLit (LList list) -> 
			let le_list = List.map (fun lit -> LLit lit) list in 
			LEList (nle1 :: le_list) 
		| _, _ -> LCons (nle1, nle2))
	
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
	
	| LLNth (le1, le2) -> 
		let nle1 = f le1 in 
		let nle2 = f le2 in 
		(match nle1, nle2 with 
		| LLit (LList list), LLit (Num n) -> (try LLit (List.nth list (int_of_float n)) with _ ->
			 raise (Failure "List index out of bounds"))
		| LEList list, LLit (Num n) -> (try (List.nth list (int_of_float n)) with _ -> 
			 raise (Failure "List index out of bounds"))
		| _, _ -> LLNth (nle1, nle2))

	| LSNth (le1, le2) -> 
		let nle1 = f le1 in 
		let nle2 = f le2 in 
		match nle1, nle2 with 
		| LLit (String s), LLit (Num n) -> (try LLit (String (String.make 1 (String.get s (int_of_float n)))) with _ ->
			 raise (Failure "String index out of bounds"))
		| _, _ -> LSNth (nle1, nle2)

let normalise_pure_assertion store gamma subst assertion =
	let fe = normalise_lexpr store gamma subst in 
	match assertion with 
	| LEq (le1, le2) -> 
		let nle1 = fe le1 in 
		let nle2 = fe le2 in 
		LEq(nle1, nle2)
	
	| LLessEq (le1, le2) ->
		let nle1 = fe le1 in 
		let nle2 = fe le2 in 
		LLessEq(nle1, nle2)
	
	| LNot (LEq (le1, le2)) -> 
		let nle1 = fe le1 in 
		let nle2 = fe le2 in 
		LNot (LEq(nle1, nle2))
	
	| LNot (LLessEq (le1, le2)) ->
		let nle1 = fe le1 in 
		let nle2 = fe le2 in 
		LNot (LLessEq(nle1, nle2)) 
	
	| _ -> raise (Failure "normalize_pure_assertion can only process pure assertions")		


(**
  var_set is a hashtbl (what else?) that models the set of variables  
*)
let rec get_expr_vars var_set e = 
	let f = get_expr_vars var_set in 
	match e with 
	| LLit _
	| LNone 
	| LVar _ 
	| ALoc _ -> ()
	| PVar var -> (try Hashtbl.find var_set var; () with _ -> Hashtbl.add var_set var true)
	| LBinOp (e1, op, e2) -> f e1; f e2
	| LUnOp (op, e1) -> f e1 
	| LEVRef	(e1, e2) 
	| LEORef (e1, e2) -> f e1; f e2
	| LBase e1 
	| LField e1
	| LTypeOf e1 -> f e1 
	| LCons (e1, e2)    
	| LLNth (e1, e2) 
	| LSNth (e1, e2) -> f e1; f e2
	| LEList le_list -> List.iter (fun le -> f le) le_list 
	

let get_expr_vars_lst le =
	let vars_tbl = Hashtbl.create 101 in
	get_expr_vars vars_tbl le; 
	Hashtbl.fold 
		(fun var v_val ac -> var :: ac)
		vars_tbl
		[]

let get_vars_tbl var_arr =  
	let len = Array.length var_arr in 
	let vars_tbl = Hashtbl.create len in
	for u=0 to (len-1) do 
		let var_u = var_arr.(u) in 
		Hashtbl.add vars_tbl var_u u 
	done; 
	vars_tbl	
			
			
let get_assertion_vars ass = 
	
	let vars_tbl = Hashtbl.create 101 in 
	
	let rec get_ass_vars_iter ass = 
		match ass with 
		| LAnd (_, _) -> raise (Failure "Unsupported assertion during normalization: LAnd")
		| LOr (_, _) -> raise (Failure "Unsupported assertion during normalization: LOr")
		| LNot a1 -> get_ass_vars_iter a1
		| LTrue
		| LFalse -> () 
		| LEq (e1, e2) 
		| LLessEq (e1, e2) -> get_expr_vars vars_tbl e1; get_expr_vars vars_tbl e2
		| LStar (a1, a2) -> get_ass_vars_iter a1; get_ass_vars_iter a2
		| LPointsTo (e1, e2, e3) -> get_expr_vars vars_tbl e1; get_expr_vars vars_tbl e2; get_expr_vars vars_tbl e3
		| LEmp -> () 
		| LExists (_, _) -> raise (Failure "Unsupported assertion during normalization: LExists")
		| LForAll (_, _) -> raise (Failure "Unsupported assertion during normalization: LForAll") in 
	
	get_ass_vars_iter ass; 
	vars_tbl 

let new_abs_loc_name var = abs_loc_prefix ^ var 

let new_lvar_name var = lvar_prefix ^ var 

let rec init_symb_store_alocs store gamma subst ass : unit =
	let f = init_symb_store_alocs store gamma subst in 
	match ass with
	| LStar (a_left, a_right) ->
		f a_left; f a_right 
		
	| LPointsTo (PVar var, _, _) ->
		(try Hashtbl.find store var; ()
		with _ ->
			(let aloc = new_abs_loc_name var in 
			Hashtbl.add store var (ALoc aloc);
			Hashtbl.add subst var (ALoc aloc); 
			Hashtbl.replace gamma var ObjectType; 
			()))
		 
	| LPointsTo (LVar var, _, _) ->
		(try (Hashtbl.find subst var); ()
			with _ ->
				(let aloc = new_abs_loc_name var in  
				Hashtbl.add subst var (ALoc aloc); 
				Hashtbl.replace gamma var ObjectType; 
				()))
				
	| LPointsTo (ALoc _, _, _) ->
		raise (Failure "Unsupported assertion during normalization")	
										
	| _ -> ()


let init_pure_assignments a store gamma subst = 
	
	let pure_assignments = Hashtbl.create 31 in 
	let non_store_pure_assertions = Stack.create () in 
	
	(**
   * After putting the variables that have assignents of the kind: 
	 * x = E (where E is a logical expression) in the store, 
	 * we have to normalize the remaining pure assertions 
	 *)
	let normalize_pure_assertions () = 
		let stack_size = Stack.length non_store_pure_assertions in 
		let non_store_pure_assertions_array = DynArray.make (stack_size*5) in 
		let cur_index = ref 0 in 
		(* Printf.printf "Stack size: %d\n" stack_size; *)
		
		while (not (Stack.is_empty non_store_pure_assertions)) do
			let pure_assertion = Stack.pop non_store_pure_assertions in 
			let normalized_pure_assertion = normalise_pure_assertion store gamma subst pure_assertion in 
			(* Printf.printf "about to put the pure assertion in the dynamic array at position %d\n" (!cur_index); *)
			DynArray.add non_store_pure_assertions_array normalized_pure_assertion; 
			(* Printf.printf "successfully put"; *)
			cur_index := (!cur_index) + 1
		done;
		
		non_store_pure_assertions_array in 
	
	
	(**
	 * Given an assertion a, this function returns the list of pure assignments in a. 
	 * assignments of the form: x = E or E = x for a logical expression E and a variable x
	 *)
	let rec get_pure_assignments_iter a = 
		(match a with 
		| LStar (a_left, a_right) -> 
			get_pure_assignments_iter a_left; 
			get_pure_assignments_iter a_right
		
		| LEq (PVar x, le) 
		| LEq (le, PVar x) ->
			if (not (Hashtbl.mem pure_assignments x))
				then Hashtbl.add pure_assignments x le
				else Stack.push (LEq (PVar x, le)) non_store_pure_assertions
		
		| LNot a -> Stack.push (LNot a) non_store_pure_assertions 
		| LLessEq (e1, e2) -> Stack.push (LLessEq (e1, e2)) non_store_pure_assertions		
		
		| _ -> ()) in 
	
	
	(**
   * all program variables not in the store need to be added there 
   *)
	let fill_store p_vars =
	Hashtbl.iter 
		(fun var _ -> 
			try Hashtbl.find store var; () with _ ->  
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
		let len = Array.length p_vars in 
		let succs = Array.make len [] in 
		
		(* Printf.printf("computing the succs\n"); *)
		for u=0 to (len-1) do 
			let cur_var = p_vars.(u) in 
			let cur_le = Hashtbl.find pure_assignments cur_var in 
			let cur_var_deps = get_expr_vars_lst cur_le in 
			(* let cur_var_deps_str = 
				List.fold_left
					(fun ac var -> 
						if (ac = "") 
							then var 
							else ac ^ "; " ^ var)
					""
					cur_var_deps in 
			
			 Printf.printf "var: %s, var_index: %s, deps: %s \n" cur_var (string_of_int u) cur_var_deps_str; *)
			let rec loop deps = 
				match deps with 
				| [] -> () 
				| v :: rest_deps -> 
					(try 
						let v_num = Hashtbl.find p_vars_tbl v in 
						succs.(u) <- v_num :: succs.(u)
					with _ -> ()); 
					loop rest_deps in 
			loop cur_var_deps
		done; 
		succs in 
	
	(** 
   * normalization of variable definitions 
	 *)	
	let normalize_pure_assignments (succs : int list array) (p_vars : string array) (p_vars_tbl : (string, int) Hashtbl.t) = 
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
			(* Printf.printf "Rewriting the assignment to variable %s\n" var; *)
			let le = try Some (Hashtbl.find pure_assignments var) with _ -> None in 
			(match le with 
			| None ->
				let msg = Printf.sprintf "Should not be here: rewrite_assignment. Var: %s\n" var in 
				raise (Failure msg)
		 	| Some le -> 
				let normalized_le = normalise_lexpr store gamma subst le in
				Hashtbl.remove subst var; 
				Hashtbl.remove pure_assignments var;  
				Hashtbl.replace store var normalized_le) in  
								
		let rec search (u : int) =
			let u_var = p_vars.(u) in
			(* Printf.printf "Visiting variable %s \n" u_var; *)
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
		
		for i=0 to (len-1) do 
			if (not (visited_tbl.(i))) 
				then search i
				else ()
		done in 	
	
	(* get the pure assignments and store them in the hashtbl pure_assignments *) 
	
	(* let str = Hashtbl.fold
		(fun key value ac -> 
			if (ac = "") then key else ac ^ "; " ^ key)
		pure_assignments
		"" in
	Printf.printf "Purely assigned variables before checking circularities: %s\n" str; *)
	get_pure_assignments_iter a;
	let p_vars = 
		Array.of_list 
			(Hashtbl.fold 
				(fun var le ac -> var :: ac) 
				pure_assignments 
				[]) in 
	let p_vars_tbl = get_vars_tbl p_vars in  
	fill_store (get_assertion_vars a);
	let succs = vars_succ p_vars p_vars_tbl in
	normalize_pure_assignments succs p_vars p_vars_tbl;   
	(* Printf.printf "after fill store \n"; *)
	normalize_pure_assertions ()
	
	
let rec compute_symb_heap (heap : symbolic_heap) (store : symbolic_store) p_formulae gamma subst a = 
	let f = compute_symb_heap heap store p_formulae gamma subst in  
	let fe = normalise_lexpr store gamma subst in 
	
	let simplify_element_of_cell_assertion ele = 
		(match ele with 
		| LLit _ 
		| LVar _ 
		| ALoc _ -> ele 
		| _ -> 
			let lvar = fresh_lvar () in 
			(* I need to add the type of the new logical variable to the gamma *) 
			DynArray.add p_formulae (LEq ((LVar lvar), ele)); 
			LVar lvar) in 
	
	match a with 
	| LStar (a1, a2) -> f a1; f a2
	
	| LPointsTo (LVar var, le2, le3) 
	| LPointsTo (PVar var, le2, le3) ->
		let aloc = (try
			(match Hashtbl.find subst var with 
			| ALoc aloc -> aloc 
			| _ -> raise (Failure "This should not happen, ever!"))
			with _ -> raise (Failure "This should not happen, ever!")) in  
		let nle2 = simplify_element_of_cell_assertion (fe le2) in 
		let nle3 = simplify_element_of_cell_assertion (fe le3) in
		let field_val_pairs, default_val = (try LHeap.find heap aloc with _ -> ([], LUnknown)) in  
		LHeap.replace heap aloc (((nle2, nle3) :: field_val_pairs), default_val)
		
	| LPointsTo (LLit (Loc loc), le2, le3) -> 
		let nle2 = simplify_element_of_cell_assertion (fe le2) in 
		let nle3 = simplify_element_of_cell_assertion (fe le3) in
		let field_val_pairs, default_val = (try LHeap.find heap loc with _ -> ([], LUnknown)) in
		LHeap.replace heap loc (((nle2, nle3) :: field_val_pairs), default_val)
	
	| LEq (_, _)
	| LLessEq (_, _) 
	| LNot (LEq (_, _)) 
	| LNot (LLessEq (_, _))
 	| LEmp -> () 
	
let rec init_gamma gamma a = 
	let f = init_gamma gamma in
	match a with
	  | LTypeEnv type_list -> 
			List.iter 
				(fun (v, t) -> 
					match v with
					| LVar v 
					| PVar v -> Hashtbl.replace gamma v t
					| _ -> raise (Failure ("Only vars or lvars in the typing environment, for the love of God.")))
				type_list
		| LStar	(al, ar) -> f al; f ar
		| _ -> ()

let normalize_assertion_top_level a = 
	
	let heap = LHeap.create 1021 in 
	let store = Hashtbl.create 1021 in 
	let gamma = Hashtbl.create 1021 in 
	let subst = Hashtbl.create 1021 in 
	
	init_gamma gamma a;
	init_symb_store_alocs store gamma subst a;
	let p_formulae = init_pure_assignments a store gamma subst in 
	compute_symb_heap heap store p_formulae gamma subst a; 
	heap, store, p_formulae, gamma
