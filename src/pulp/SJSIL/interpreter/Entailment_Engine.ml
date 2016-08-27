open Z3
open JSIL_Syntax

(** Retrieve the jsil_type corresponding to a bin_op *)
let type_of_binary_operator op =
	match op with
	(* FIXME: These could be NumberType *)
	| Plus  -> IntType
	| Minus -> IntType
	| Times -> IntType
	| Div   -> IntType
	| Mod   -> IntType
	| _     -> raise (Failure "SMT encoding: Construct not supported yet!")

(** Retrieve the jsil_type corresponding to a unary_op *)
let type_of_unary_operator op =
	match op with
	(* FIXME: This could be NumberType *)
	| UnaryMinus  -> IntType
	| _           -> raise (Failure "SMT encoding: Construct not supported yet!")

(** Retrieve the jsil_type corresponding to a jsil_logic_expr *)
let type_of_logic_expr gamma expr =
	match expr with
	| LLit llit          -> JSIL_Interpreter.evaluate_type_of llit
	| LNone              -> NoneType
	| LVar var           ->
		(try Hashtbl.find gamma var with
		| _ -> raise (Failure "Type of logical variable not found in the environment: FIRE"))
	| ALoc _             -> ObjectType
	| PVar _             -> raise (Failure "Program variable in pure formula: FIRE")
	| LBinOp (_, op, _)  -> type_of_binary_operator op
	| LUnOp (op, _)      -> type_of_unary_operator op
	| _                  -> raise (Failure "SMT encoding: Construct not supported yet!")


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
	Arithmetic.Real.mk_numeral_s ctx (string_of_float value)

(** Encode strings as Z3 numerical constants *)
let str_codes = Hashtbl.create 1000
let str_counter = ref 0
let encode_string ctx str =
	try Hashtbl.find str_codes str with
	| Not_found ->
		(* New string: add it to the hashtable *)
		let z3_code = Arithmetic.Integer.mk_numeral_i ctx !str_counter in
		str_counter := !str_counter + 1;
		Hashtbl.add str_codes str z3_code;
		z3_code

(** Encode JSIL literals as Z3 numerical constants *)
let encode_literal ctx lit =
	match lit with
	| Undefined  -> Arithmetic.Integer.mk_numeral_i ctx 0
	| Null       -> Arithmetic.Integer.mk_numeral_i ctx 1
	| Empty      -> Arithmetic.Integer.mk_numeral_i ctx 2
	| Constant c -> encode_constant ctx c
	| Bool b     -> Boolean.mk_val ctx b
	| Integer i  -> Arithmetic.Integer.mk_numeral_i ctx i
	| Num n      ->
		if (n = (snd (modf n)))
			then Arithmetic.Integer.mk_numeral_i ctx (int_of_float n)
			else Arithmetic.Real.mk_numeral_s ctx (string_of_float n)
	| String s   -> encode_string ctx s
	| Loc l      -> encode_string ctx ("$l" ^ l)
	| Type t     -> encode_type ctx t
	| _          -> raise (Failure "SMT encoding: Construct not supported yet!")

(** Encode JSIL binary operators *)
let encode_binop ctx op le1 le2 =
	match op with
	| Plus  -> (Arithmetic.mk_add ctx [ le1; le2 ])
	| Minus -> (Arithmetic.mk_sub ctx [ le1; le2 ])
	| Times -> (Arithmetic.mk_mul ctx [ le1; le2 ])
	| Div   -> (Arithmetic.mk_div ctx le1 le2)
	| Mod   -> (Arithmetic.Integer.mk_mod ctx le1 le2)
	| _     -> raise (Failure "SMT encoding: Construct not supported yet!")

(** Encode JSIL unary operators *)
let encode_unop ctx op le = 
	match op with 
	| UnaryMinus -> (Arithmetic.mk_unary_minus ctx le)
	| _          -> raise (Failure "SMT encoding: Construct not supported yet!")

(** Encode JSIL logical expressions *)
let rec encode_logical_expression ctx gamma e =
	let ele = encode_logical_expression ctx gamma in
	(match e with
	| LLit lit              -> encode_literal ctx lit
	| LNone                 -> Arithmetic.Integer.mk_numeral_i ctx 3
	| LVar var
	| ALoc var              -> Arithmetic.Integer.mk_const_s ctx var
	| PVar _                -> raise (Failure "Program variable in pure formula: FIRE")
	| LBinOp (le1, op, le2) -> encode_binop ctx op (ele le1) (ele le2)
	| LUnOp (op, le)        -> encode_unop ctx op (ele le)
(*| LTypeOf le            ->
		FuncDecl.apply
			(FuncDecl.mk_func_decl_s ctx "typeOf" [???] (sort_of_type ctx TypeType))
			[(ele le)]*)
	| _                     -> raise (Failure "Failure - z3 encoding: Unsupported logical expression"))

let rec encode_pure_formula ctx gamma a =
	let f = encode_pure_formula ctx gamma in
	let fe = encode_logical_expression ctx gamma in
	match a with
	| LNot a             -> Boolean.mk_not ctx (f a)
	| LEq (le1, le2)     ->
		if (type_of_logic_expr gamma le1) = (type_of_logic_expr gamma le2)
			then Boolean.mk_eq ctx (fe le1) (fe le2)
			else Boolean.mk_false ctx
	| LLess (le1, le2)   -> Arithmetic.mk_lt ctx (fe le1) (fe le2)
	| LLessEq (le1, le2) -> Arithmetic.mk_le ctx (fe le1) (fe le2)
	| LStrLess (_, _)    -> raise (Failure ("I don't know how to do string comparison in Z3"))
	| _                  -> raise (Failure ("Unsupported assertion to enconde for Z3"))


let check_entailment left_as right_as gamma =
	let cfg = [("model", "true"); ("proof", "false")] in
	let ctx = (mk_context cfg) in
	let right_as = List.map 
			(fun a -> 
				let a = encode_pure_formula ctx gamma a in
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
			(fun a -> encode_pure_formula ctx gamma a)
			left_as in 
	List.iter
		(fun expr -> Printf.printf "Z3 Expression: %s\n" (Expr.to_string expr))
		(left_as @ [ right_as_or ]);
	let solver = (Solver.mk_solver ctx None) in
	Solver.add solver (left_as @ [ right_as_or ]);
	Printf.printf "I checked what I had to check\n";
	let ret = (if (Solver.check solver []) != Solver.SATISFIABLE then true else false) in 
	Gc.full_major (); 
	Solver.reset solver; 
	ret
