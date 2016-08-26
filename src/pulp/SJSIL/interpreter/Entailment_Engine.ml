open Z3
open JSIL_Syntax

(* Get a Z3 sort from a JSIL type *)
let sort_of_type ctx t =
	match t with
	| UndefinedType         -> Sort.mk_uninterpreted_s ctx "UndefinedSort"
	| NullType              -> Sort.mk_uninterpreted_s ctx "NullSort"
	| EmptyType             -> Sort.mk_uninterpreted_s ctx "EmptySort"
	| NoneType              -> Sort.mk_uninterpreted_s ctx "NoneSort"
  | BooleanType           -> Boolean.mk_sort ctx
	| IntType               -> Arithmetic.Integer.mk_sort ctx
  | NumberType            -> Arithmetic.Real.mk_sort ctx
	| StringType            -> Sort.mk_uninterpreted_s ctx "StringSort"
  | ObjectType            -> Sort.mk_uninterpreted_s ctx "ObjectSort"
	| ReferenceType         -> Sort.mk_uninterpreted_s ctx "ReferenceSort"
	| ObjectReferenceType   -> Sort.mk_uninterpreted_s ctx "ObjectReferenceSort"
	| VariableReferenceType -> Sort.mk_uninterpreted_s ctx "VariableReferenceSort"
	| ListType              -> Sort.mk_uninterpreted_s ctx "ListSort"
	| TypeType              -> Sort.mk_uninterpreted_s ctx "TypeSort"


(** Encode JSIL type literals as Z3 constants of sort TypeSort *)
let encode_type ctx jsil_type =
	let type_sort = sort_of_type ctx TypeType in
	match jsil_type with
	| UndefinedType         -> Expr.mk_const_s ctx "UndefinedType" type_sort
	| NullType              -> Expr.mk_const_s ctx "NullType" type_sort
	| EmptyType             -> Expr.mk_const_s ctx "EmptyType" type_sort
	| NoneType              -> Expr.mk_const_s ctx "NoneType" type_sort
  | BooleanType           -> Expr.mk_const_s ctx "BooleanType" type_sort
	| IntType               -> Expr.mk_const_s ctx "IntType" type_sort
  | NumberType            -> Expr.mk_const_s ctx "NumberType" type_sort
	| StringType            -> Expr.mk_const_s ctx "StringType" type_sort
  | ObjectType            -> Expr.mk_const_s ctx "ObjectType" type_sort
	| ReferenceType         -> Expr.mk_const_s ctx "ReferenceType" type_sort
	| ObjectReferenceType   -> Expr.mk_const_s ctx "ObjectReferenceType" type_sort
	| VariableReferenceType -> Expr.mk_const_s ctx "VariableReferenceType" type_sort
	| ListType              -> Expr.mk_const_s ctx "ListType" type_sort
	| TypeType              -> Expr.mk_const_s ctx "TypeType" type_sort

(** Encode JSIL constants as Z3 constants of sort Arithmetic.Real *)
let encode_constant ctx constant =
	let float_sort = sort_of_type ctx NumberType in
	match constant with
	| Min_float -> Expr.mk_const_s ctx "Min_float" float_sort
	| Max_float -> Expr.mk_const_s ctx "Max_float" float_sort
	| Random    -> Expr.mk_const_s ctx "Random" float_sort
	| E         -> Expr.mk_const_s ctx "E" float_sort
	| Ln10      -> Expr.mk_const_s ctx "Ln10" float_sort
	| Ln2       -> Expr.mk_const_s ctx "Ln2" float_sort
	| Log2e     -> Expr.mk_const_s ctx "Log2e" float_sort
	| Log10e    -> Expr.mk_const_s ctx "Log10e" float_sort
	| Pi        -> Expr.mk_const_s ctx "Pi" float_sort
	| Sqrt1_2   -> Expr.mk_const_s ctx "Sqrt1_2" float_sort
	| Sqrt2     -> Expr.mk_const_s ctx "Sqrt2" float_sort

(** Encode JSIL literals as constants of the corresponding sort *)
let encode_literal ctx lit =
	match lit with
	| Undefined  -> Expr.mk_const_s ctx "Undefined" (sort_of_type ctx UndefinedType)
	| Null       -> Expr.mk_const_s ctx "Null" (sort_of_type ctx NullType)
	| Empty      -> Expr.mk_const_s ctx "Empty" (sort_of_type ctx EmptyType)
	| Constant c -> encode_constant ctx c
	| Bool b     -> Boolean.mk_val ctx b
	| Integer i  -> Arithmetic.Integer.mk_numeral_i ctx i
	| Num n      -> Arithmetic.Real.mk_numeral_s ctx (string_of_float n)
	| String s   -> Expr.mk_const_s ctx s (sort_of_type ctx StringType)
  | Loc l      -> Expr.mk_const_s ctx l (sort_of_type ctx ObjectType)
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
	| LNone                 -> Expr.mk_const_s ctx "None" (sort_of_type ctx NoneType)
	| LVar var              ->
		let var_type =
			(try Hashtbl.find gamma var with
			| _ -> raise (Failure (Printf.sprintf "Logical variables must be typed. Could not find type of %s.\n" var))) in 
		Expr.mk_const_s ctx var (sort_of_type ctx var_type)
	| ALoc aloc             -> Expr.mk_const_s ctx aloc (sort_of_type ctx ObjectType)
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
		let le1_sort = Expr.get_sort (fe le1) in
		let le2_sort = Expr.get_sort (fe le2) in
		(if Sort.equal le1_sort le2_sort
			then Boolean.mk_eq ctx (fe le1) (fe le2)
			else Boolean.mk_false ctx)
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
			else
				(List.nth right_as 0) in 
	let left_as = 
		List.map 
			(fun a -> encode_pure_formula ctx gamma a)
			left_as in 
	let solver = (Solver.mk_solver ctx None) in
	Solver.add solver (left_as @ [ right_as_or ]);
	Printf.printf "I checked what I had to check\n";
	(if (Solver.check solver []) != Solver.SATISFIABLE then true else false)
