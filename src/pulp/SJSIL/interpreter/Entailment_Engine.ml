open Z3
open JSIL_Syntax


(** Encode JSIL type literals as Z3 numerical constants *)
let encode_type ctx jsil_type =
	match jsil_type with
	| UndefinedType         -> Arithmetic.Integer.mk_numeral_i ctx 0
	| NullType              -> Arithmetic.Integer.mk_numeral_i ctx 1
	| EmptyType             -> Arithmetic.Integer.mk_numeral_i ctx 2
	| NoneType              -> Arithmetic.Integer.mk_numeral_i ctx 3
  | BooleanType           -> Arithmetic.Integer.mk_numeral_i ctx 4
	| IntType               -> Arithmetic.Integer.mk_numeral_i ctx 5
  | NumberType            -> Arithmetic.Integer.mk_numeral_i ctx 6
	| StringType            -> Arithmetic.Integer.mk_numeral_i ctx 7
  | ObjectType            -> Arithmetic.Integer.mk_numeral_i ctx 8
	| ReferenceType         -> Arithmetic.Integer.mk_numeral_i ctx 9
	| ObjectReferenceType   -> Arithmetic.Integer.mk_numeral_i ctx 10
	| VariableReferenceType -> Arithmetic.Integer.mk_numeral_i ctx 11
	| ListType              -> Arithmetic.Integer.mk_numeral_i ctx 12
	| TypeType              -> Arithmetic.Integer.mk_numeral_i ctx 13

(** Encode JSIL constants as Z3 numerical constants *)
let encode_constant ctx constant =
	let value =
		(match JSIL_Interpreter.evaluate_constant constant with
		| Num v -> v
		| _     -> raise (Failure "SMT encoding: Unknown constant")) in
	(Arithmetic.Real.mk_numeral_s ctx (string_of_float value)), (encode_type ctx NumberType)

(** Encode strings as Z3 numerical constants *)
let str_codes = Hashtbl.create 1000
let str_counter = ref 0
let encode_string ctx str =
	(* Printf.printf "I am going to encode a string\n"; *)
	try 
		let str_number = Hashtbl.find str_codes str in 
		(* Printf.printf "the string is already there!"; *)
		let z3_code = Arithmetic.Integer.mk_numeral_i ctx str_number in 
		z3_code
	with Not_found ->
		(* New string: add it to the hashtable *)
		let z3_code = Arithmetic.Integer.mk_numeral_i ctx !str_counter in
		Hashtbl.add str_codes str (!str_counter);
		str_counter := !str_counter + 1;
		z3_code

(** Encode JSIL literals as Z3 numerical constants *)
let encode_literal ctx lit =
	match lit with
	| Undefined  -> (Arithmetic.Integer.mk_numeral_i ctx 0), (encode_type ctx UndefinedType)
	| Null       -> (Arithmetic.Integer.mk_numeral_i ctx 1), (encode_type ctx NullType)
	| Empty      -> (Arithmetic.Integer.mk_numeral_i ctx 2), (encode_type ctx EmptyType)
	| Constant c -> encode_constant ctx c
	| Bool b     ->
		(match b with
		| true     -> (Arithmetic.Integer.mk_numeral_i ctx 0), (encode_type ctx BooleanType)
		| false    -> (Arithmetic.Integer.mk_numeral_i ctx 1), (encode_type ctx BooleanType))
	| Integer i  -> (Arithmetic.Integer.mk_numeral_i ctx i), (encode_type ctx IntType)
	| Num n      ->
		if (n = (snd (modf n)))
			then        (Arithmetic.Integer.mk_numeral_i ctx (int_of_float n)), (encode_type ctx IntType)
			else        (Arithmetic.Real.mk_numeral_s ctx (string_of_float n)), (encode_type ctx NumberType)
	| String s   -> (encode_string ctx s), (encode_type ctx StringType)
	| Loc l      -> (encode_string ctx ("$l" ^ l)), (encode_type ctx ObjectType)
	| Type t     -> (encode_type ctx t), (encode_type ctx TypeType)
	| _          -> raise (Failure "SMT encoding: Construct not supported yet - literal!")

(** Encode JSIL binary operators *)
let encode_binop ctx op le1 le2 =
	match op with
	| Plus          -> (Arithmetic.mk_add ctx [ le1; le2 ])
	| Minus         -> (Arithmetic.mk_sub ctx [ le1; le2 ])
	| Times         -> (Arithmetic.mk_mul ctx [ le1; le2 ])
	| Div           -> (Arithmetic.mk_div ctx le1 le2)
	| Mod           -> (Arithmetic.Integer.mk_mod ctx le1 le2)
	| _     -> 
		let msg = Printf.sprintf "SMT encoding: Construct not supported yet - binop - %s!" (JSIL_Print.string_of_binop op) in 
		raise (Failure msg)

(** Encode JSIL unary operators *)
let encode_unop ctx op le = 
	match op with 
	| UnaryMinus -> (Arithmetic.mk_unary_minus ctx le)
	| _          -> 
		let msg = Printf.sprintf "SMT encoding: Construct not supported yet - unop - %s!" (JSIL_Print.string_of_unop op) in 
		raise (Failure msg)
		
	

(** Encode JSIL logical expressions *)
let rec encode_logical_expression ctx gamma z3_typeof_fun e =
	let ele = encode_logical_expression ctx gamma z3_typeof_fun in
	(match e with
	| LLit lit        -> 
		let le, te = encode_literal ctx lit in 
		le, te, []
	
	| LNone           -> 
		let le, te = (Arithmetic.Integer.mk_numeral_i ctx 3), (encode_type ctx NoneType) in
		le, te, []
	
	| LVar var
	| ALoc var        -> 
		let le = Arithmetic.Integer.mk_const_s ctx var in 
		let te = Expr.mk_app ctx z3_typeof_fun [ le ] in 
		le, te, []
		
	| PVar _          -> raise (Failure "Program variable in pure formula: FIRE")
	
	| LBinOp (le1, op, le2) -> 
		let le1, te1, as1 = ele le1 in 
		let le2, te2, as2 = ele le2 in
		let le = encode_binop ctx op le1 le2 in 
		let as_op = Boolean.mk_eq ctx te1 te2 in 
		le, te1, (as_op :: (as1 @ as2))
		
	| LUnOp (op, le)  -> 
		let le, te, as1 = ele le in 
		let le = encode_unop ctx op le in 
		le, te, as1
						
	| _                     -> raise (Failure "Failure - z3 encoding: Unsupported logical expression"))


let rec encode_pure_formula ctx gamma z3_typeof_fun a =
	let f = encode_pure_formula ctx gamma z3_typeof_fun in
	let fe = encode_logical_expression ctx gamma z3_typeof_fun in
	match a with
	| LNot a             -> Boolean.mk_not ctx (f a)
	
	| LEq (le1, le2)     ->
		let t1, _ = JSIL_Logic_Normalise.normalised_is_typable gamma le1 in 
		let t2, _ = JSIL_Logic_Normalise.normalised_is_typable gamma le2 in
		let le1, te1, as1 = fe le1 in 
		let le2, te2, as2 = fe le2 in 
		(match t1, t2 with 
		| Some t1, Some t2 -> 
			if (t1 = t2)  
				then Boolean.mk_eq ctx le1 le2
				else Boolean.mk_false ctx
		| _, _ ->
			let cur_as1 = Boolean.mk_eq ctx le1 le2 in 
			let cur_as2 = Boolean.mk_eq ctx te1 te2 in 
			Boolean.mk_and ctx ([ cur_as1; cur_as2 ] @ as1 @ as2))
	
	| LLess (le1, le2)   -> 
		let t1, _ = JSIL_Logic_Normalise.normalised_is_typable gamma le1 in 
		let t2, _ = JSIL_Logic_Normalise.normalised_is_typable gamma le2 in
		let le1, te1, as1 = fe le1 in 
		let le2, te2, as2 = fe le2 in 
		(match t1, t2 with 
		| Some t1, Some t2 -> 
			let t = types_lub t1 t2 in 
			match t with 
			| Some IntType
			| Some NumberType -> Arithmetic.mk_lt ctx le1 le2
			| _ -> raise (Failure "Arithmetic operation invoked on non-numeric types"))
	
	| LLessEq (le1, le2) -> 
		let le1, te1, as1 = fe le1 in 
		let le2, te2, as2 = fe le2 in 
		Arithmetic.mk_le ctx le1 le2
		
	| LStrLess (_, _)    -> raise (Failure ("I don't know how to do string comparison in Z3"))

	| LTrue              -> Boolean.mk_true ctx
	
	| LFalse             -> Boolean.mk_false ctx

	| _                  -> 
		let msg = Printf.sprintf "Unsupported assertion to encode for Z3: %s" (JSIL_Print.string_of_logic_assertion a false) in 
		raise (Failure msg)


let check_satisfiability assertions gamma = 
	let cfg = [("model", "true"); ("proof", "false")] in
	let ctx = (mk_context cfg) in
	
	let z3_typeof_fun_name = (Symbol.mk_string ctx "typeof") in
	let z3_typeof_fun_domain = [ Arithmetic.Integer.mk_sort ctx ] in
	let z3_typeof_fun = FuncDecl.mk_func_decl ctx z3_typeof_fun_name z3_typeof_fun_domain (Arithmetic.Integer.mk_sort ctx) in 
	
	let assertions = 
		List.map 
			(fun a -> 
				(* Printf.printf "I am about to check the satisfiablity of: %s\n" (JSIL_Print.string_of_logic_assertion a false); *)
				let a = encode_pure_formula ctx gamma z3_typeof_fun a in 
				(* Printf.printf "Z3 Expression: %s\n" (Expr.to_string a); *)
				a)
			assertions in 
	let solver = (Solver.mk_solver ctx None) in
	Solver.add solver assertions;
	let ret = (Solver.check solver []) = Solver.SATISFIABLE in 
	Gc.full_major (); 
	Solver.reset solver;
	ret


(* right_as must be satisfiable *)
let check_entailment left_as right_as gamma =
	let cfg = [("model", "true"); ("proof", "false")] in
	let ctx = (mk_context cfg) in

	let z3_typeof_fun_name = (Symbol.mk_string ctx "typeof") in
	let z3_typeof_fun_domain = [ Arithmetic.Integer.mk_sort ctx ] in
	let z3_typeof_fun = FuncDecl.mk_func_decl ctx z3_typeof_fun_name z3_typeof_fun_domain (Arithmetic.Integer.mk_sort ctx) in 

	let ret_right = check_satisfiability right_as gamma in 
	if (not (ret_right)) then false 
	else 	
		begin 
	
		(* check if left_as => right_as *)
		let right_as = List.map 
				(fun a -> 
					(* Printf.printf "I am about to encode a pure formula inside the check_entailment: %s\n" (JSIL_Print.string_of_logic_assertion a false); *) 
					let a = encode_pure_formula ctx gamma z3_typeof_fun a in
					(* Printf.printf "Z3 Expression: %s\n" (Expr.to_string a); *)
					(* Printf.printf "I encoded a pure formula successfully\n"; *)
					Boolean.mk_not ctx a)
				right_as in 
		let right_as_or = 
			if ((List.length right_as) > 1) then 
					(Boolean.mk_or ctx right_as) 
				else if ((List.length right_as) = 1) then
					(List.nth right_as 0) 
				else Boolean.mk_false ctx in 
		let left_as = 
			List.map 
				(fun a -> encode_pure_formula ctx gamma z3_typeof_fun a)
				left_as in 
		(* List.iter
			(fun expr -> Printf.printf "Z3 Expression: %s\n" (Expr.to_string expr))
			(left_as @ [ right_as_or ]); *)	
		let solver = (Solver.mk_solver ctx None) in
		Solver.add solver (left_as @ [ right_as_or ]);
		let ret = (Solver.check solver []) != Solver.SATISFIABLE in 
		(* Printf.printf "ret: %s\n" (string_of_bool ret); *)
		Gc.full_major (); 
		Solver.reset solver; 
		ret
		end 