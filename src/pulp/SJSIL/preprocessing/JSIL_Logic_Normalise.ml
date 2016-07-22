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
  

let llvar_prefix = "_$l_"
let lvar_prefix = "_lvar_"

let fresh_llvar = fresh_sth llvar_prefix 
let fresh_lvar = fresh_sth lvar_prefix 


let rec normalize_lexpr le store symb_loc_tbl = 
	match le with 
	| LLit lit -> LLit lit
	| LNone -> LNone
	| LVar lvar -> (try LLVar (Hashtbl.find symb_loc_tbl lvar) with _ -> LVar lvar)
	| LLVar llvar -> raise (Failure "Unsupported expression during normalization: LLVar")
	| PVar pvar -> 
		(try Hashtbl.find store pvar with
		|  _ -> 
			let msg = Printf.sprintf "Program variable %s not found: sth went wrong" pvar in 
			raise (Failure msg))
	
	| LBinOp (le1, bop, le2) -> 
		let nle1 = normalize_lexpr le1 store symb_loc_tbl in 
		let nle2 = normalize_lexpr le2 store symb_loc_tbl in 
		(match nle1, nle2 with 
		| LLit lit1, LLit lit2 ->
			let lit = SJSIL_Interpreter.evaluate_binop bop lit1 lit2 in 
			LLit lit
		| _, _ -> LBinOp (nle1, bop, nle2))

	| LUnOp (uop, le1) -> 
		let nle1 = normalize_lexpr le1 store symb_loc_tbl in 
		(match nle1 with 
		| LLit lit1 -> 
			let lit = SJSIL_Interpreter.evaluate_unop uop lit1 in 
			LLit lit 
		| _ -> LUnOp (uop, nle1))

	| _ -> raise (Failure "Program variable not found: sth went wrong")
		
	| LEVRef (le1, le2) ->
		let nle1 = normalize_lexpr le1 store symb_loc_tbl in 
		let nle2 = normalize_lexpr le2 store symb_loc_tbl in 
		(match nle1, nle2 with 
		| LLit l, LLit (String field) -> LLit (LVRef (l, field))
		| _, _ -> LEVRef (nle1, nle2))
	
	| LEORef (le1, le2) ->
		let nle1 = normalize_lexpr le1 store symb_loc_tbl in 
		let nle2 = normalize_lexpr le2 store symb_loc_tbl in 
		(match nle1, nle2 with 
		| LLit l, LLit (String field) -> LLit (LORef (l, field))
		| _, _ -> LEORef (nle1, nle2))
	
	| LBase	(le1) -> 
		let nle1 = normalize_lexpr le1 store symb_loc_tbl in 
		(match nle1 with 
		| LLit (LVRef (l, _)) 
		| LLit (LORef (l, _)) -> LLit l
		| LEVRef (leb, _) 
		| LEORef (leb, _) -> leb
		| _ -> LBase (nle1))
	
	| LField	(le1) -> 
		let nle1 = normalize_lexpr le1 store symb_loc_tbl in 
		(match nle1 with 
		| LLit (LVRef (_, f)) 
		| LLit (LORef (_, f)) -> LLit (String f)
		| LEVRef (_, fe) 
		| LEORef (_, fe) -> fe
		| _ -> LField (nle1))	
				
	| LTypeOf (le1) -> 
		let nle1 = normalize_lexpr le1 store symb_loc_tbl in 
		(match nle1 with 
		| LLit llit -> LLit (Type (SJSIL_Interpreter.evaluate_type_of llit)) 
		| LNone -> raise (Failure "Illegal Logic Expression: TypeOf of None")
		| LVar _ -> LTypeOf (nle1)
		| LLVar _ -> LTypeOf (nle1)
		| PVar _ -> raise (Failure "This should never happen: program variable in normalized expression") 
		| LBinOp (_, _, _)   
		| LUnOp (_, _) -> LTypeOf (nle1)
		| LEVRef (_, _) -> LLit (Type VariableReferenceType)
		| LEORef (_, _) -> LLit (Type ObjectReferenceType)
		| LBase _ -> LLit (Type ObjectType)
		| LField _ -> LLit (Type StringType)
		| LTypeOf _ -> LLit (Type TypeType))
		

let normalize_pure_assertion assertion store symb_tbl = 
	match assertion with 
	| LEq (le1, le2) -> 
		let nle1 = normalize_lexpr le1 store symb_tbl in 
		let nle2 = normalize_lexpr le2 store symb_tbl in 
		LEq(nle1, nle2)
	
	| LLessEq (le1, le2) ->
		let nle1 = normalize_lexpr le1 store symb_tbl in 
		let nle2 = normalize_lexpr le2 store symb_tbl in
		LLessEq(nle1, nle2)
	
	| LNot (LEq (le1, le2)) -> 
		let nle1 = normalize_lexpr le1 store symb_tbl in 
		let nle2 = normalize_lexpr le2 store symb_tbl in
		LNot (LEq(nle1, nle2))
	
	| LNot (LLessEq (le1, le2)) ->
		let nle1 = normalize_lexpr le1 store symb_tbl in 
		let nle2 = normalize_lexpr le2 store symb_tbl in
		LNot (LLessEq(nle1, nle2)) 
	
	| _ -> raise (Failure "normalize_pure_assertion can only process pure assertions")		


let rec get_expr_vars e var_tbl = 
	match e with 
	| LLit _
	| LNone 
	| LVar _ 
	| LLVar _ -> ()
	| PVar var -> (try Hashtbl.find var_tbl var; () with _ -> Hashtbl.add var_tbl var true)
	| LBinOp (e1, op, e2) -> get_expr_vars e1 var_tbl; get_expr_vars e2 var_tbl
	| LUnOp (op, e1) -> get_expr_vars e1 var_tbl
	| LEVRef	(e1, e2) 
	| LEORef (e1, e2) -> get_expr_vars e1 var_tbl; get_expr_vars e2 var_tbl
	| LBase e1 
	| LField e1
	| LTypeOf e1 -> get_expr_vars e1 var_tbl
	
let get_expr_vars_lst le =
	let vars_tbl = Hashtbl.create 101 in
	get_expr_vars le vars_tbl; 
	Hashtbl.fold 
		(fun var v_val ac -> var :: ac)
		vars_tbl
		[]

let get_vars_tbl var_arr = 
	let vars_tbl = Hashtbl.create 101 in 
	let len = Array.length var_arr in 
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
		| LLessEq (e1, e2) -> get_expr_vars e1 vars_tbl; get_expr_vars e2 vars_tbl
		| LStar (a1, a2) -> get_ass_vars_iter a1; get_ass_vars_iter a2
		| LPointsTo (e1, e2, e3) -> get_expr_vars e1 vars_tbl; get_expr_vars e2 vars_tbl; get_expr_vars e3 vars_tbl
		| LEmp -> () 
		| LExists (_, _) -> raise (Failure "Unsupported assertion during normalization: LExists")
		| LForAll (_, _) -> raise (Failure "Unsupported assertion during normalization: LForAll") in 
	
	get_ass_vars_iter ass; 
	vars_tbl 

let new_llvar_name var = llvar_prefix ^ var 

let new_lvar_name var = lvar_prefix ^ var 

let rec init_symb_store_llvars ass symb_tbl store : unit =
	match ass with
	| LStar (a_left, a_right) ->
		init_symb_store_llvars a_left symb_tbl store; 
		init_symb_store_llvars a_right symb_tbl store  
		
	| LPointsTo (PVar var, _, _) ->
		(try Hashtbl.find store var; ()
		with _ ->
			let llvar = new_llvar_name var in 
			Hashtbl.add store var (LLVar llvar);
			Hashtbl.add symb_tbl var llvar)
		 
	| LPointsTo (LVar var, _, _) ->
		(try Hashtbl.find symb_tbl var; ()
			with _ ->
				let llvar = new_llvar_name var in  
				Hashtbl.add symb_tbl var llvar)
				
	| LPointsTo (LLVar _, _, _) ->
		raise (Failure "Unsupported assertion during normalization")	
										
	| _ -> ()


let init_pure_assignments a store symb_tbl = 
	
	let pure_assignments = Hashtbl.create 31 in 
	let non_store_pure_assertions = Stack.create () in 
	let a_vars = get_assertion_vars a in 
	
	(**
   * After putting the the variables that have assignents of the kind: x = E (where E is a logical expression)
	 * in the store. We have to normalize the remaining pure assertions 
	 *)
	let normalize_pure_assertions () = 
		let stack_size = Stack.length non_store_pure_assertions in 
		let non_store_pure_assertions_array = DynArray.make (stack_size*5) in 
		let cur_index = ref 0 in 
		
		Printf.printf "Stack size: %d\n" stack_size; 
		
		while (not (Stack.is_empty non_store_pure_assertions)) do
			let index = !cur_index in 
			let pure_assertion =  Stack.pop non_store_pure_assertions in 
			let normalized_pure_assertion = normalize_pure_assertion pure_assertion store symb_tbl in 
			Printf.printf "about to put the pure assertion in the dynamic array at position %d\n" index; 
			DynArray.add non_store_pure_assertions_array normalized_pure_assertion; 
			Printf.printf "successfully put"; 
			cur_index := index + 1
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
				then Hashtbl.replace pure_assignments x le
				else Stack.push (LEq (PVar x, le)) non_store_pure_assertions
		
		| LNot a -> Stack.push (LNot a) non_store_pure_assertions 
		| LLessEq (e1, e2) -> Stack.push (LLessEq (e1, e2)) non_store_pure_assertions		
		
		| _ -> ()) in 
	
	
	(**
   * all program variables in a that are not in the store need to be added to the 
	 * store 
   *)
	let fill_store p_vars =
	Hashtbl.iter 
		(fun var _ -> 
			try Hashtbl.find store var; () with _ ->  
				let new_l_var = new_lvar_name var in 
				Hashtbl.add store var (LVar new_l_var); 
				Hashtbl.add symb_tbl var new_l_var)
		p_vars	in 
	
	(**
   * dependency graphs between variable definitions 
   *)
	let vars_succ p_vars p_vars_tbl = 
		let len = Array.length p_vars in 
		let succs = Array.make len [] in 
		
		Printf.printf("computing the succs\n");
		
		for u=0 to (len-1) do 
			
			let cur_var = p_vars.(u) in 
			let cur_le = Hashtbl.find pure_assignments cur_var in 
			let cur_var_deps = get_expr_vars_lst cur_le in 
			let cur_var_deps_str = 
				List.fold_left
					(fun ac var -> 
						if (ac = "") 
							then var 
							else ac ^ "; " ^ var)
					""
					cur_var_deps in 
			
			(* Printf.printf "var: %s, var_index: %s, deps: %s \n" cur_var (string_of_int u) cur_var_deps_str; *)
			
			let rec loop cur_var_deps_iter = 
				match cur_var_deps_iter with 
				| [] -> () 
				| v :: rest_deps -> 
					let v_num = (try Some (Hashtbl.find p_vars_tbl v) with _ -> None) in
					(match v_num with 
					| Some v_num -> succs.(u) <- v_num :: succs.(u)  
					| None -> ()); 
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
		
		let remove_assignment var = 
			let new_l_var = try Some (Hashtbl.find symb_tbl var) with _ -> None in  
			let le = try Some (Hashtbl.find pure_assignments var) with _ -> None in 
			(match new_l_var, le with 
			| None, _ 	
			| _, None -> 
				let msg = Printf.sprintf "Should not be here: remove_assignment. Var: %s." var in 
				raise (Failure msg)
			| Some new_l_var, Some le ->  
				Stack.push (LEq ((LVar new_l_var), le)) non_store_pure_assertions;
				Hashtbl.remove pure_assignments var) in  
		
		let rewrite_assignment var = 
			Printf.printf "Rewriting the assignment to variable %s\n" var; 
			let le = try Some (Hashtbl.find pure_assignments var) with _ -> None in 
			(match le with 
			| None ->
				let msg = Printf.sprintf "Should not be here: rewrite_assignment. Var: %s\n" var in 
				raise (Failure msg)
		 	| Some le -> 
				let normalized_le = normalize_lexpr le store symb_tbl in
				Hashtbl.remove symb_tbl var; 
				Hashtbl.remove pure_assignments var;  
				Hashtbl.replace store var normalized_le) in  
								
		let rec search (u : int) =
			let u_var = p_vars.(u) in
			Printf.printf "Visiting variable %s \n" u_var; 
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
	
	(* got the pure assignments and store them in the hashtbl pure_assignments *) 
	get_pure_assignments_iter a;
	let str = Hashtbl.fold
		(fun key value ac -> 
			if (ac = "") then key else ac ^ "; " ^ key)
		pure_assignments
		"" in
	Printf.printf "Purely assigned variables before checking circularities: %s\n" str; 
	let p_vars = 
		Array.of_list 
			(Hashtbl.fold 
				(fun var le ac -> var :: ac) 
				pure_assignments 
				[]) in 
	let p_vars_tbl = get_vars_tbl p_vars in  
	fill_store a_vars;
	let succs = vars_succ p_vars p_vars_tbl in
	normalize_pure_assignments succs p_vars p_vars_tbl;   
	Printf.printf "after fill store \n"; 
	normalize_pure_assertions ()
	
	
let rec compute_symb_heap a (heap : symbolic_heap) (store : symbolic_store) symb_tbl = 
	match a with 
	| LStar (a1, a2) -> 
		compute_symb_heap a1 heap store symb_tbl; 
		compute_symb_heap a2 heap store symb_tbl
	
	| LPointsTo (LVar var, le2, le3) 
	| LPointsTo (PVar var, le2, le3) ->
		let llvar = (try Hashtbl.find symb_tbl var 
			with _ -> raise (Failure "This should not happen, ever!")) in  
		let nle2 = normalize_lexpr le2 store symb_tbl in 
		let nle3 = normalize_lexpr le3 store symb_tbl in
		let field_val_pairs, default_val = (try LHeap.find heap llvar with _ -> ([], Some LNone)) in  
		LHeap.replace heap llvar (((nle2, nle3) :: field_val_pairs), default_val)
		
	| LPointsTo (LLit (Loc loc), le2, le3) -> 
		let nle2 = normalize_lexpr le2 store symb_tbl in 
		let nle3 = normalize_lexpr le3 store symb_tbl in
		let field_val_pairs, default_val = (try LHeap.find heap loc with _ -> ([], Some LNone)) in
		LHeap.replace heap loc (((nle2, nle3) :: field_val_pairs), default_val)
	
	| LEq (_, _)
	| LLessEq (_, _) 
	| LNot (LEq (_, _)) 
	| LNot (LLessEq (_, _))
 	| LEmp -> () 
	

let normalize_assertion_top_level a = 
	
	let heap = LHeap.create 1021 in 
	let store = Hashtbl.create 1021 in 
	let symb_tbl = Hashtbl.create 1021 in 
	
	init_symb_store_llvars a symb_tbl store;
	let p_formulae = init_pure_assignments a store symb_tbl in 
	Printf.printf "after init pure assignments \n"; 
	compute_symb_heap a heap store symb_tbl; 
	heap, store, p_formulae
