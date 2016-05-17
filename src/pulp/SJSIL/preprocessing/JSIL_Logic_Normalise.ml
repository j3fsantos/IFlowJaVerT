open JSIL_Logic_Syntax 
open DynArray

let fresh_variable =
  let counter = ref 0 in
  let rec f name =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f

let fresh_logical_variable () =
  fresh_variable "_lvar_"

let llvar_prefix = "$l_"


let rec normalize_lexpr le store symb_loc_tbl = 
	match le with 
	| LLit lit -> LLit lit
	| LNone -> LNone
	| LListEmpty -> LListEmpty
	| LVar lvar -> (try LLVar (Hashtbl.find symb_loc_tbl lvar) with _ -> LVar lvar)
	| LLVar llvar -> raise (Failure "Unsupported expression during normalization: LLVar")
	| PVar pvar -> (try Hashtbl.find store pvar with _ -> raise (Failure "Program variable not found: sth went wrong"))
	
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
		| LLit (Loc loc), LLit (String field) -> LLit (LVRef (loc, field))
		| _, _ -> LEVRef (nle1, nle2))
	
	| LEORef (le1, le2) ->
		let nle1 = normalize_lexpr le1 store symb_loc_tbl in 
		let nle2 = normalize_lexpr le2 store symb_loc_tbl in 
		(match nle1, nle2 with 
		| LLit (Loc loc), LLit (String field) -> LLit (LORef (loc, field))
		| _, _ -> LEORef (nle1, nle2))
	
	| LBase	(le1) -> 
		let nle1 = normalize_lexpr le1 store symb_loc_tbl in 
		(match nle1 with 
		| LLit (LVRef (loc, _)) 
		| LLit (LORef (loc, _)) -> LLit (Loc loc)
		| LEVRef (leb, _) 
		| LEORef (leb, _) -> leb
		| _ -> LBase (nle1))
		
	| LTypeOf (le1) -> 
		let nle1 = normalize_lexpr le1 store symb_loc_tbl in 
		(match nle1 with 
		| LLit llit -> LLit (Type (SJSIL_Interpreter.evaluate_type_of llit)) 
		| LNone -> raise (Failure "Illegal Logic Expression: TypeOf of None")
		| LListEmpty -> raise (Failure "Illegal Logic Expression: TypeOf of Logic List") 
		| LVar _ -> LTypeOf (nle1)
		| LLVar _ -> LTypeOf (nle1)
		| PVar _ -> raise (Failure "This should never happen: program variable in normalized expression") 
		| LBinOp (_, _, _)   
		| LUnOp (_, _) -> LTypeOf (nle1)
		| LEVRef (_, _) -> LLit (Type VariableReferenceType)
		| LEORef (_, _) -> LLit (Type ObjectReferenceType)
		| LBase _ -> LLit (Type ObjectType)
		| LField _ -> LLit (Type StringType)
		| LTypeOf _ -> LLit (Type TypeType) 
		| LCons (_, _) -> raise (Failure "This should never happen: program variable in normalized expression"))
	
	| LCons (le1, le2) -> 
		let nle1 = normalize_lexpr le1 store symb_loc_tbl in 
		let nle2 = normalize_lexpr le2 store symb_loc_tbl in 
		LCons (nle1, nle2)
	
let rec get_expr_vars e var_tbl = 
	match e with 
	| LLit _
	| LNone 
	| LListEmpty 
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
	| LCons (e1, e2) -> get_expr_vars e1 var_tbl; get_expr_vars e2 var_tbl		


let get_ass_vars ass = 
	
	let vars_tbl = Hashtbl.create 1021 in 
	
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

let rec init_symb_locations ass symb_loc_table lstore : unit =
	match ass with
	| LStar (ass_left, ass_right) ->
		init_symb_locations ass_left symb_loc_table lstore;
		init_symb_locations ass_right symb_loc_table lstore  
		
	| LPointsTo (PVar var, _, _) ->
		(try Hashtbl.find lstore var; () 
		with _ -> 
			Hashtbl.add lstore var (LLVar (llvar_prefix ^ var));
			Hashtbl.add symb_loc_table var (llvar_prefix ^ var))
		 
	| LPointsTo (LVar var, _, _) ->
		(try Hashtbl.find symb_loc_table var; ()
			with _ -> Hashtbl.add symb_loc_table var (llvar_prefix ^ var))
				
	| LPointsTo (LLVar _, _, _) ->
		raise (Failure "Unsupported assertion during normalization")
		
	| _ -> ()


let fill_abs_store ass lstore =  
	let pvars = get_ass_vars ass in 	
	Hashtbl.iter 
		(fun var _ -> 
			try Hashtbl.find lstore var; () with _ -> 
				let new_l_var = fresh_logical_variable () in 
				Hashtbl.add lstore var (LVar new_l_var))
		pvars


let rec normalize_assertion ass heap store p_formulae symb_loc_table = 
	match ass with 
	| LStar (a1, a2) -> 
		normalize_assertion a1 heap store p_formulae symb_loc_table; 
		normalize_assertion a2 heap store p_formulae symb_loc_table
	
	| LPointsTo (LVar var, le2, le3) 
	| LPointsTo (PVar var, le2, le3) ->
		let llvar = (try Hashtbl.find symb_loc_table var 
			with _ -> raise (Failure "This should not happen, ever!")) in  
		let nle2 = normalize_lexpr le2 store symb_loc_table in 
		let nle3 = normalize_lexpr le3 store symb_loc_table in
		let field_val_pairs = (try Hashtbl.find heap llvar with _ -> []) in  
		Hashtbl.replace heap llvar ((nle2, nle3) :: field_val_pairs)
		
	| LPointsTo (LLit (Loc loc), le2, le3) -> 
		let nle2 = normalize_lexpr le2 store symb_loc_table in 
		let nle3 = normalize_lexpr le3 store symb_loc_table in
		let field_val_pairs = (try Hashtbl.find heap loc with _ -> []) in
		Hashtbl.replace heap loc ((nle2, nle3) :: field_val_pairs)

 	| LEmp -> () 
	
	| LEq (le1, le2) -> 
		let nle1 = normalize_lexpr le1 store symb_loc_table in 
		let nle2 = normalize_lexpr le2 store symb_loc_table in 
		DynArray.add p_formulae (LEq(nle1, nle2)) 
	
	| LLessEq (le1, le2) ->
		let nle1 = normalize_lexpr le1 store symb_loc_table in 
		let nle2 = normalize_lexpr le2 store symb_loc_table in
		DynArray.add p_formulae (LLessEq(nle1, nle2)) 
	
	| LNot (LEq (le1, le2)) -> 
		let nle1 = normalize_lexpr le1 store symb_loc_table in 
		let nle2 = normalize_lexpr le2 store symb_loc_table in
		DynArray.add p_formulae (LNot (LEq(nle1, nle2)))
	
	| LNot (LLessEq (le1, le2)) ->
		let nle1 = normalize_lexpr le1 store symb_loc_table in 
		let nle2 = normalize_lexpr le2 store symb_loc_table in
		DynArray.add p_formulae (LNot (LLessEq(nle1, nle2))) 
	
	| _ -> raise (Failure "Unsupported assertion during normalization")


let normalize_assertion_top_level ass = 
	
	let heap = Hashtbl.create 1021 in 
	let store = Hashtbl.create 1021 in 
	let symb_tbl = Hashtbl.create 1021 in 
	let p_formulae = DynArray.create () in 
	
	init_symb_locations ass symb_tbl store;
	fill_abs_store ass store;  
	normalize_assertion ass heap store p_formulae symb_tbl; 
	heap, store, p_formulae
