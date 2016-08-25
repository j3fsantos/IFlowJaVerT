open Z3
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.Boolean
open Z3.FuncDecl
open Z3.Goal
open Z3.Tactic
open Z3.Tactic.ApplyResult
open Z3.Probe
open Z3.Solver
open Z3.Arithmetic
open Z3.Arithmetic.Integer
open Z3.Arithmetic.Real
open Z3.BitVector
open JSIL_Syntax

let encode_string_as_num ctx str_codes str =
	let str_counter = ref 0 in
	let str_code_offset = 100 in
	try Hashtbl.find str_codes str
	with Not_found ->
		let z3_code = mk_numeral_i ctx (!str_counter + str_code_offset) in
		str_counter := !str_counter + 1;
		Hashtbl.add str_codes str z3_code;
		z3_code

let encode_type_as_sort ctx jsil_type = 
	match jsil_type with 
	| BooleanType -> (Boolean.mk_sort ctx)
	| IntType -> (Integer.mk_sort ctx)
	| NumberType -> (Real.mk_sort ctx) 
	| _ -> raise (Failure "type not supported yet")

let encode_literal ctx str_codes lit = 
	match lit with 
	| Undefined -> encode_string_as_num ctx str_codes "undefined"

	| Null -> encode_string_as_num ctx str_codes "null"
		
	| Empty -> encode_string_as_num ctx str_codes "empty"

	| Bool b -> 
		(match b with 
		| true -> (mk_true ctx)
		| false -> (mk_false ctx))
	
	| Num n -> 
		if (n = (snd (modf n))) 
			then (mk_numeral_int ctx (int_of_float n) (Integer.mk_sort ctx))
			else (Real.mk_numeral_s ctx (string_of_float n))
			
	| Integer i -> (mk_numeral_int ctx i (Integer.mk_sort ctx))
	
	| String s -> encode_string_as_num ctx str_codes ("string_" ^ s)	
		
  | Loc l -> encode_string_as_num ctx str_codes ("loc_" ^ l)

  | Type t -> encode_string_as_num ctx str_codes ("type_" ^ (JSIL_Print.string_of_type t))
	
	| _ -> raise (Failure "smt encoding: Construct not supported yet!")


let encode_binop ctx op le1 le2 = 
	match op with 
	| Plus -> (Arithmetic.mk_add ctx [ le1; le2 ])
	| Minus -> (Arithmetic.mk_sub ctx [ le1; le2 ]) 
	| Times -> (Arithmetic.mk_mul ctx [ le1; le2 ]) 
	| Div -> (Arithmetic.mk_div ctx le1 le2) 
	| Mod -> (Arithmetic.Integer.mk_mod ctx le1 le2) 
	| _ -> raise (Failure "smt encoding: Construct not supported yet!")


let encode_unop ctx op le = 
	match op with 
	| UnaryMinus -> (mk_neg ctx le) 
	| _ -> raise (Failure "smt encoding: Construct not supported yet!")


let rec encode_logical_expression ctx gamma str_codes e = 
	let fl = encode_literal ctx str_codes in 
	let f = encode_logical_expression ctx gamma str_codes in 
	(match e with 
	| LLit lit -> fl lit 
	| LNone -> encode_string_as_num ctx str_codes "lnone"
	| LVar var -> 
		let var_type = 
			try Hashtbl.find gamma var with _ -> raise (Failure "Logical variables must be typed") in 
		let var_sort = encode_type_as_sort ctx var_type in 
		let var_name = (Symbol.mk_string ctx var) in	
		let var_expr = (Expr.mk_const ctx var_name var_sort) in
		var_expr
	| ALoc aloc -> encode_string_as_num ctx str_codes ("aloc_" ^ aloc)
	| PVar _ -> raise (Failure "Program variable in pure formula: FIRE")
	| LBinOp (le1, op, le2) -> encode_binop ctx op (f le1) (f le2) 
	| LUnOp (op, le) -> encode_unop ctx op (f le) 
	| _ -> raise (Failure "Failure - z3 encoding: Unsupported logical expression"))
  

let rec encode_pure_formula ctx gamma str_codes a = 
	let f = encode_pure_formula ctx gamma str_codes in 
	let fe = encode_logical_expression ctx gamma str_codes in 
	match a with 
	| LEq (le1, le2) -> (mk_eq ctx (fe le1) (fe le2))
	| LLess (le1, le2) -> (mk_lt ctx (fe le1) (fe le2))
	| LLessEq (le1, le2) -> (Boolean.mk_not ctx (mk_gt ctx (fe le1) (fe le2)))
	| LNot a -> (Boolean.mk_not ctx (f a))
	| LStrLess (_, _) -> raise (Failure ("I don't know how to do string comparison in Z3"))
	| _ -> raise (Failure ("Unsupported assertion to enconde for Z3"))


let check_entailment left_as right_as gamma =
	let string_codes = Hashtbl.create 100 in
	let cfg = [("model", "true"); ("proof", "false")] in
	let ctx = (mk_context cfg) in
	let right_as = List.map 
			(fun a -> 
				let a = encode_pure_formula ctx gamma string_codes a in 
				Boolean.mk_not ctx a)
			right_as in 
	let right_as_or = 
		if ((List.length right_as) > 1) then 
				(Boolean.mk_or ctx right_as) 
			else
				(List.nth right_as 0) in 
	let left_as = 
		List.map 
			(fun a -> encode_pure_formula ctx gamma string_codes a)
			left_as in 
	let solver = (mk_solver ctx None) in
	(*let g = (mk_goal ctx true false false) in	
	Goal.add g (left_as @ [ right_as_or ]); 
	(List.iter (fun a -> (Solver.add solver [ a ])) (get_formulas g)); *)
	Solver.add solver (left_as @ [ right_as_or ]);
	Printf.printf "I checked what I had to check\n";
	(if (check solver []) != SATISFIABLE then true else false)
