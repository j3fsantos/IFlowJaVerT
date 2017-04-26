open JSIL_Syntax
open Symbolic_State
open JSIL_Logic_Utils
open Z3



type encoding =
 | WithReals
 | WithFPA

let string_of_enc enc =
	match enc with
 	| WithReals -> "REAL"
 	| WithFPA -> "FPA"

let encoding = ref WithReals

let match_enc msg x y =
	match (!encoding) with
	| WithReals -> x
	| WithFPA   -> y


type jsil_axiomatized_operations = {
	typeof_fun          : FuncDecl.func_decl;
	llen_fun            : FuncDecl.func_decl;
	slen_fun            : FuncDecl.func_decl;
	num2str_fun         : FuncDecl.func_decl;
	str2num_fun         : FuncDecl.func_decl;
	num2int_fun         : FuncDecl.func_decl;
	lnth_fun            : FuncDecl.func_decl;
	snth_fun            : FuncDecl.func_decl;
}

type jsil_type_constructors = {
	undefined_type_constructor : FuncDecl.func_decl;
	null_type_constructor      : FuncDecl.func_decl;
	empty_type_constructor     : FuncDecl.func_decl;
	none_type_constructor      : FuncDecl.func_decl;
	boolean_type_constructor   : FuncDecl.func_decl;
	number_type_constructor    : FuncDecl.func_decl;
	string_type_constructor    : FuncDecl.func_decl;
	object_type_constructor    : FuncDecl.func_decl;
  	list_type_constructor      : FuncDecl.func_decl;
  	type_type_constructor      : FuncDecl.func_decl
}

type jsil_value_constructors = {
	nil_constructor       : FuncDecl.func_decl;
	cons_constructor      : FuncDecl.func_decl;
	undefined_constructor : FuncDecl.func_decl;
	null_constructor      : FuncDecl.func_decl;
	empty_constructor     : FuncDecl.func_decl;
	boolean_constructor   : FuncDecl.func_decl;
	number_constructor    : FuncDecl.func_decl;
	string_constructor    : FuncDecl.func_decl;
  	loc_constructor       : FuncDecl.func_decl;
  	type_constructor      : FuncDecl.func_decl;
  	list_constructor      : FuncDecl.func_decl;
  	none_constructor      : FuncDecl.func_decl;
  	boolean_accessor      : FuncDecl.func_decl;
	number_accessor       : FuncDecl.func_decl;
  	string_accessor       : FuncDecl.func_decl;
  	list_accessor         : FuncDecl.func_decl
}



let cfg = [("model", "true"); ("proof", "true"); ("unsat_core", "true")] 
let ctx : Z3.context = (mk_context cfg) 

let booleans_sort = Boolean.mk_sort ctx 
let ints_sort     = Arithmetic.Integer.mk_sort ctx
let reals_sort    = Arithmetic.Real.mk_sort ctx  
let fp_sort       = FloatingPoint.mk_sort_64 ctx
let numbers_sort  = match_enc "mk_sort" reals_sort fp_sort

let rm = FloatingPoint.mk_const ctx (Symbol.mk_string ctx "rm") (FloatingPoint.RoundingMode.mk_sort ctx)
let mk_string_symb s = Symbol.mk_string ctx s

let mk_int_i = Arithmetic.Integer.mk_numeral_i ctx 
let mk_const      = match_enc "mk_const" (Arithmetic.Real.mk_const ctx)     (fun (s : Symbol.symbol) -> FloatingPoint.mk_const ctx s fp_sort)
let mk_num_i      = match_enc "mk_num_i" (Arithmetic.Real.mk_numeral_i ctx) (fun i -> FloatingPoint.mk_numeral_i ctx i fp_sort)
let mk_num_s      = match_enc "mk_num_s" (Arithmetic.Real.mk_numeral_s ctx) (fun s -> FloatingPoint.mk_numeral_s ctx s fp_sort)
let mk_lt         = match_enc "mk_lt"    Arithmetic.mk_lt             FloatingPoint.mk_lt
let mk_le         = match_enc "mk_le"    Arithmetic.mk_le             FloatingPoint.mk_leq
let mk_ge         = match_enc "mk_ge"    Arithmetic.mk_ge             FloatingPoint.mk_geq

let mk_add = match_enc "mk_add" (fun e1 e2 -> Arithmetic.mk_add ctx [e1; e2]) (fun e1 e2 -> FloatingPoint.mk_add ctx rm e1 e2)
let mk_sub = match_enc "mk_sub" (fun e1 e2 -> Arithmetic.mk_sub ctx [e1; e2]) (fun e1 e2 -> FloatingPoint.mk_sub ctx rm e1 e2)
let mk_mul = match_enc "mk_mul" (fun e1 e2 -> Arithmetic.mk_mul ctx [e1; e2]) (fun e1 e2 -> FloatingPoint.mk_mul ctx rm e1 e2)
let mk_div = match_enc "mk_div" (fun e1 e2 -> Arithmetic.mk_div ctx  e1  e2 ) (fun e1 e2 -> FloatingPoint.mk_div ctx rm e1 e2)


let z3_jsil_type_sort = 
	Enumeration.mk_sort 
		ctx 
		(mk_string_symb "JSIL_Type")
		(List.map mk_string_symb 
			[ 
				"UndefinedType"; "NullType"; "EmptyType"; "NoneType"; "BooleanType"; 
				"NumberType"; "StringType"; "ObjectType"; "ListType"; "TypeType"	
			])


let type_operations = 
	try 	
		let z3_jsil_type_constructors  = Datatype.get_constructors z3_jsil_type_sort in 
		let undefined_type_constructor = List.nth z3_jsil_type_constructors 0 in 
		let null_type_constructor      = List.nth z3_jsil_type_constructors 1 in 
		let empty_type_constructor     = List.nth z3_jsil_type_constructors 2 in 
		let none_type_constructor      = List.nth z3_jsil_type_constructors 3 in 
		let boolean_type_constructor   = List.nth z3_jsil_type_constructors 4 in 
		let number_type_constructor    = List.nth z3_jsil_type_constructors 5 in 
		let string_type_constructor    = List.nth z3_jsil_type_constructors 6 in 
		let object_type_constructor    = List.nth z3_jsil_type_constructors 7 in 
		let list_type_constructor      = List.nth z3_jsil_type_constructors 8 in 
		let type_type_constructor      = List.nth z3_jsil_type_constructors 9 in 
		{
			undefined_type_constructor = undefined_type_constructor;
			null_type_constructor      = null_type_constructor; 
			empty_type_constructor     = empty_type_constructor; 
			none_type_constructor      = none_type_constructor; 
			boolean_type_constructor   = boolean_type_constructor; 
			number_type_constructor    = number_type_constructor; 
			string_type_constructor    = string_type_constructor; 
			object_type_constructor    = object_type_constructor; 
			list_type_constructor      = list_type_constructor; 
			type_type_constructor      = type_type_constructor	
		}
											
	with _ -> raise (Failure ("DEATH: type_operations")) 


let z3_jsil_literal_sort, z3_jsil_list_sort, lit_operations = 
	(* JSIL type constructors *)
	let jsil_undefined_constructor = 
		Datatype.mk_constructor ctx (mk_string_symb "Undefined") (mk_string_symb "isUndefined") [] [] [] in 
	let jsil_null_constructor = 
		Datatype.mk_constructor ctx (mk_string_symb "Null") (mk_string_symb "isNull") [] [] [] in 
	let jsil_empty_constructor = 
		Datatype.mk_constructor ctx (mk_string_symb "Empty") (mk_string_symb "isEmpty") [] [] [] in 
	let jsil_bool_constructor = 
		Datatype.mk_constructor ctx (mk_string_symb "Bool") (mk_string_symb "isBool") 
			[ (mk_string_symb "value") ] [ Some booleans_sort ] [ 0 ] in
	let jsil_num_constructor = 
		Datatype.mk_constructor ctx (mk_string_symb "Num") (mk_string_symb "isNum") 
			[ (mk_string_symb "value") ] [ Some numbers_sort ] [ 0 ] in
	let jsil_string_constructor = 
		Datatype.mk_constructor ctx (mk_string_symb "String") (mk_string_symb "isString") 
			[ (mk_string_symb "value") ] [ Some ints_sort ] [ 0 ] in
	let jsil_loc_constructor = 
		Datatype.mk_constructor ctx (mk_string_symb "Loc") (mk_string_symb "isLoc") 
			[ (mk_string_symb "value") ] [ Some ints_sort ] [ 0 ] in
	let jsil_type_constructor = 
		Datatype.mk_constructor ctx (mk_string_symb "Type") (mk_string_symb "isType") 
			[ (mk_string_symb "value") ] [ Some ints_sort ] [ 0 ] in
	let jsil_list_constructor = 
		Datatype.mk_constructor ctx (mk_string_symb "List") (mk_string_symb "isList") 
			[ (mk_string_symb "value") ] [ None ] [ 1 ] in
	let jsil_none_constructor = 
		Datatype.mk_constructor ctx (mk_string_symb "None") (mk_string_symb "isNone") [] [] [] in

	(* JSIL List Type constructors *)
	let jsil_list_nil_constructor = 
		Datatype.mk_constructor ctx (mk_string_symb "Nil") (mk_string_symb "isNil") [] [] [] in 
	let jsil_list_cons_constructor = 
		Datatype.mk_constructor ctx (mk_string_symb "Cons") (mk_string_symb "isCons") 
			[ (mk_string_symb "head"); (mk_string_symb "tail") ] [ None; None ] [ 0; 1] in 

	let literal_and_literal_list_sorts = 
		Datatype.mk_sorts  
			ctx
			[ (mk_string_symb "JSIL_Literal"); (mk_string_symb "JSIL_Literal_List") ]
			[
				[
					jsil_undefined_constructor; 
					jsil_null_constructor;
					jsil_empty_constructor; 
					jsil_bool_constructor; 
					jsil_num_constructor; 
					jsil_string_constructor; 
					jsil_loc_constructor; 
					jsil_type_constructor; 
					jsil_list_constructor; 
					jsil_none_constructor
				]; 

				[
					jsil_list_nil_constructor; 
					jsil_list_cons_constructor
				]
			] in 

	try 
		let z3_jsil_literal_sort = List.nth literal_and_literal_list_sorts 0 in 
		let z3_jsil_list_sort    = List.nth literal_and_literal_list_sorts 1 in 

		let z3_jsil_list_constructors = Datatype.get_constructors z3_jsil_list_sort in 
		let nil_constructor           = List.nth z3_jsil_list_constructors 0 in 
		let cons_constructor          = List.nth z3_jsil_list_constructors 1 in 
			
		let z3_literal_constructors   = Datatype.get_constructors z3_jsil_literal_sort in 
		let undefined_constructor     = List.nth z3_literal_constructors 0 in 
		let null_constructor          = List.nth z3_literal_constructors 1 in 
		let empty_constructor         = List.nth z3_literal_constructors 2 in 
		let boolean_constructor       = List.nth z3_literal_constructors 3 in 
		let number_constructor        = List.nth z3_literal_constructors 4 in
		let string_constructor        = List.nth z3_literal_constructors 5 in 
		let loc_constructor           = List.nth z3_literal_constructors 6 in 
		let type_constructor          = List.nth z3_literal_constructors 7 in 
		let list_constructor          = List.nth z3_literal_constructors 8 in 	
		let none_constructor          = List.nth z3_literal_constructors 9 in 	

		let jsil_literal_accessors    = Datatype.get_accessors z3_jsil_literal_sort in 
		let boolean_accessor          = List.nth (List.nth jsil_literal_accessors 3) 0 in 
		let number_accessor           = List.nth (List.nth jsil_literal_accessors 4) 0 in 
		let string_accessor           = List.nth (List.nth jsil_literal_accessors 5) 0 in 
		let list_accessor             = List.nth (List.nth jsil_literal_accessors 8) 0 in 
		
		let jsil_literal_operations   = {
			nil_constructor       = nil_constructor; 
			cons_constructor      = cons_constructor; 
			undefined_constructor = undefined_constructor; 
			null_constructor      = null_constructor; 
			empty_constructor     = empty_constructor; 
			boolean_constructor   = boolean_constructor; 
			number_constructor    = number_constructor; 
			string_constructor    = string_constructor; 
			loc_constructor       = loc_constructor; 
			type_constructor      = type_constructor; 
			list_constructor      = list_constructor; 
			none_constructor      = none_constructor; 
			boolean_accessor      = boolean_accessor; 
			number_accessor       = number_accessor; 
			string_accessor       = string_accessor; 
			list_accessor         = list_accessor								
		}  in 
		z3_jsil_literal_sort, z3_jsil_list_sort, jsil_literal_operations
	with _ -> raise (Failure ("DEATH: construction of z3_jsil_value_sort")) 


let axiomatised_operations = 
	
	let typeof_fun      = FuncDecl.mk_func_decl ctx (mk_string_symb "typeof")        
							[ z3_jsil_literal_sort ] z3_jsil_type_sort in
	let slen_fun        = FuncDecl.mk_func_decl ctx (mk_string_symb "s-len")         
							[ numbers_sort ] numbers_sort in
	let llen_fun        = FuncDecl.mk_func_decl ctx (mk_string_symb "l-len")         
							[ z3_jsil_list_sort ] numbers_sort in
	let num2str_fun     = FuncDecl.mk_func_decl ctx (mk_string_symb "num2str") 
							[ numbers_sort ] numbers_sort in
	let str2num_fun     = FuncDecl.mk_func_decl ctx (mk_string_symb "str2num")  
							[ numbers_sort ] numbers_sort in
	let num2int_fun     = FuncDecl.mk_func_decl ctx (mk_string_symb "num2int")   
							[ numbers_sort ] numbers_sort in
	let snth_fun        = FuncDecl.mk_func_decl ctx (mk_string_symb "s-nth")   
							[ numbers_sort; numbers_sort ] numbers_sort in
	let lnth_fun        = FuncDecl.mk_func_decl ctx (mk_string_symb "l-nth")   
							[ z3_jsil_list_sort; numbers_sort ] z3_jsil_literal_sort in
	{
		typeof_fun   = typeof_fun; 
		slen_fun     = slen_fun; 
		llen_fun     = llen_fun; 
		num2str_fun  = num2str_fun; 
		str2num_fun  = str2num_fun; 
		num2int_fun  = num2int_fun; 
		snth_fun     = snth_fun; 
		lnth_fun     = lnth_fun
	}		



let mk_z3_list_core les list_nil list_cons =
	let empty_list = Expr.mk_app ctx list_nil [ ] in
	let rec loop les cur_list =
		match les with
		| [] -> cur_list
		| le :: rest_les ->
			let new_cur_list = Expr.mk_app ctx list_cons [ le; cur_list ] in
			loop rest_les new_cur_list in
	let result = loop les empty_list in
	result

let mk_z3_list les nil_constructor cons_constructor =
	try 
		
		mk_z3_list_core (List.rev les) nil_constructor cons_constructor
	with _ -> raise (Failure "DEATH: mk_z3_list")

let str_codes = Hashtbl.create 1000
let str_counter = ref 0
let encode_string str =
	try
		let str_number = Hashtbl.find str_codes str in
		let z3_code = mk_int_i str_number in
		z3_code
	with Not_found ->
		(* New string: add it to the hashtable *)
		let z3_code = mk_int_i !str_counter in
		Hashtbl.add str_codes str (!str_counter);
		str_counter := !str_counter + 1;
		z3_code


let encode_type t =
	try 
		let z3_jsil_type_constructors = Datatype.get_constructors z3_jsil_type_sort in 
		match t with 
		| UndefinedType -> Expr.mk_app ctx type_operations.undefined_type_constructor []
		| NullType      -> Expr.mk_app ctx type_operations.null_type_constructor      []
		| EmptyType     -> Expr.mk_app ctx type_operations.empty_type_constructor     []
		| NoneType      -> Expr.mk_app ctx type_operations.none_type_constructor      []
		| BooleanType   -> Expr.mk_app ctx type_operations.boolean_type_constructor   []
		| NumberType    -> Expr.mk_app ctx type_operations.number_type_constructor    []	
		| StringType    -> Expr.mk_app ctx type_operations.string_type_constructor    []	
		| ObjectType    -> Expr.mk_app ctx type_operations.object_type_constructor    []	
		| ListType      -> Expr.mk_app ctx type_operations.list_type_constructor      []	
		| TypeType      -> Expr.mk_app ctx type_operations.type_type_constructor      []	
	with _ -> 
		raise (Failure "DEATH: encode_type") 


let rec encode_lit lit =
	try 
		match lit with
		| Undefined -> Expr.mk_app ctx lit_operations.undefined_constructor []
		| Null      -> Expr.mk_app ctx lit_operations.null_constructor      []
		| Empty     -> Expr.mk_app ctx lit_operations.empty_constructor     []
		| Bool b -> 
			let b_arg = 
				match b with 
				| true  -> Boolean.mk_true ctx 
				| false -> Boolean.mk_false ctx in 
			(Expr.mk_app ctx lit_operations.boolean_constructor [ b_arg ])
		| Num n -> 
			let sfn = string_of_float n in
			let n_arg = mk_num_s sfn in 
			(Expr.mk_app ctx lit_operations.number_constructor [ n_arg ])
		| String s -> 
			let s_arg = encode_string s in 
			(Expr.mk_app ctx lit_operations.string_constructor [ s_arg ])
		| Loc l -> 
			let l_arg = encode_string l in 
			(Expr.mk_app ctx lit_operations.loc_constructor [ l_arg ])
		| Type t -> 
			let t_arg = encode_type t in 
			(Expr.mk_app ctx lit_operations.type_constructor [ t_arg ])
		| LList lits -> 
			let args = List.map encode_lit lits in 
			let arg_list = mk_z3_list args lit_operations.nil_constructor lit_operations.cons_constructor in		
			(Expr.mk_app ctx lit_operations.list_constructor [ arg_list ])
	with _ -> 
		raise (Failure "DEATH: encode_type") 


(** Encode JSIL binary operators *)
let encode_binop op le1 le2 =
	
	let binop_numbers_to_numbers mk_op le1 le2 = 
		let n_le1 = (Expr.mk_app ctx lit_operations.number_accessor [ le1 ]) in 	
		let n_le2 = (Expr.mk_app ctx lit_operations.number_accessor [ le2 ]) in 
		let nle1_op_nle2 = mk_op n_le1 n_le2 in 
		(Expr.mk_app ctx lit_operations.number_constructor [ nle1_op_nle2 ]) in 

	let binop_numbers_to_booleans mk_op le1 le2 = 
		let n_le1 = (Expr.mk_app ctx lit_operations.number_accessor [ le1 ]) in 	
		let n_le2 = (Expr.mk_app ctx lit_operations.number_accessor [ le2 ]) in 
		let nle1_op_nle2 = mk_op n_le1 n_le2 in 
		(Expr.mk_app ctx lit_operations.boolean_constructor [ nle1_op_nle2 ]) in 

	match op with
	| Plus     -> binop_numbers_to_numbers mk_add le1 le2
	| Minus    -> binop_numbers_to_numbers mk_sub le1 le2
	| Times    -> binop_numbers_to_numbers mk_mul le1 le2
	| Div      -> binop_numbers_to_numbers mk_div le1 le2
	
	| LessThan      -> binop_numbers_to_booleans (mk_lt ctx) le1 le2
	| LessThanEqual -> binop_numbers_to_booleans (mk_le ctx) le1 le2


	| Equal    -> Expr.mk_app ctx lit_operations.boolean_constructor [ (Boolean.mk_eq ctx le1 le2) ]

	| LstCons  -> 
		let le2_list = Expr.mk_app ctx lit_operations.list_accessor [ le2 ] in  
		let new_list = Expr.mk_app ctx lit_operations.cons_constructor [ le1; le2_list ] in 
		Expr.mk_app ctx lit_operations.list_constructor [ new_list ]

	| _ -> raise (Failure "SMT encoding: Construct not supported yet - binop!")


let encode_unop op le =
	match op with

	| UnaryMinus ->
		let le_n    = Expr.mk_app ctx lit_operations.number_accessor [ le ] in 
		let op_le_n = Arithmetic.mk_unary_minus ctx le_n in
		Expr.mk_app ctx lit_operations.number_constructor [ op_le_n ]
	
	| LstLen     -> 
		let le_lst      = Expr.mk_app ctx lit_operations.list_accessor  [ le ] in 
		let op_le_lst   = Expr.mk_app ctx axiomatised_operations.llen_fun [ le_lst ] in
		Expr.mk_app ctx lit_operations.number_constructor [ op_le_lst ]

	| StrLen     -> 
		let le_s      = Expr.mk_app ctx lit_operations.string_accessor  [ le ] in 
		let op_le_s   = Expr.mk_app ctx axiomatised_operations.slen_fun [ le_s ] in
		Expr.mk_app ctx lit_operations.number_constructor [ op_le_s ]

	| ToStringOp -> 
		let le_n      = Expr.mk_app ctx lit_operations.number_accessor  [ le ] in 
		let op_le_n   = Expr.mk_app ctx axiomatised_operations.num2str_fun [ le_n ] in
		Expr.mk_app ctx lit_operations.number_constructor [ op_le_n ]

	| ToNumberOp -> 
		let le_s      = Expr.mk_app ctx lit_operations.string_accessor  [ le ] in 
		let op_le_s   = Expr.mk_app ctx axiomatised_operations.str2num_fun [ le_s ] in
		Expr.mk_app ctx lit_operations.number_constructor [ op_le_s ]

	| ToIntOp    -> 
		let le_n      = Expr.mk_app ctx lit_operations.number_accessor  [ le ] in 
		let op_le_n   = Expr.mk_app ctx axiomatised_operations.num2int_fun [ le_n ] in
		Expr.mk_app ctx lit_operations.number_constructor [ op_le_n ]	

	| Not        -> 
		let le_b      = Expr.mk_app ctx lit_operations.boolean_accessor  [ le ] in 
		let op_le_b	  = Boolean.mk_not ctx le_b in 
		Expr.mk_app ctx lit_operations.boolean_constructor [ op_le_b ]		

	| _          ->
		Printf.printf "SMT encoding: Construct not supported yet - unop - %s!\n" (JSIL_Print.string_of_unop op);
		let msg = Printf.sprintf "SMT encoding: Construct not supported yet - unop - %s!" (JSIL_Print.string_of_unop op) in
		raise (Failure msg)


let rec encode_logical_expression le =
	
	(* print_debug (Printf.sprintf "ELE: %s" (JSIL_Print.string_of_logic_expression e false)); *)
	let f = encode_logical_expression in 
	
	match le with
	| LLit lit -> encode_lit lit 

	| LNone    -> Expr.mk_app ctx lit_operations.none_constructor []

	| LVar var -> Expr.mk_const ctx (mk_string_symb var) z3_jsil_literal_sort

	| ALoc var -> Expr.mk_const ctx (mk_string_symb var) z3_jsil_literal_sort

	| PVar _   -> raise (Failure "Program variable in pure formula: FIRE")

	| LBinOp (le1, op, le2) -> encode_binop op (f le1) (f le2)
	
	| LUnOp (op, le) -> encode_unop op (f le)

	| LEList les ->
		let args = List.map f les in
		let arg_list = mk_z3_list args lit_operations.nil_constructor lit_operations.cons_constructor in		
		Expr.mk_app ctx lit_operations.list_constructor [ arg_list ]

	| LLstNth (lst, index)  ->
	    let lst'   = Expr.mk_app ctx lit_operations.list_accessor  [ (f lst) ] in
	    let index' = Expr.mk_app ctx lit_operations.number_accessor  [ (f index) ] in  
		Expr.mk_app ctx axiomatised_operations.lnth_fun [ lst'; index' ] 

	| LStrNth (str, index)  ->
		let str'   = Expr.mk_app ctx lit_operations.string_accessor  [ (f str) ] in
	    let index' = Expr.mk_app ctx lit_operations.number_accessor  [ (f index) ] in  
	    let res    = Expr.mk_app ctx axiomatised_operations.snth_fun [ str'; index' ] in 
	   	Expr.mk_app ctx lit_operations.string_constructor [ res ] 

	| LTypeOf le ->
		let res = Expr.mk_app ctx axiomatised_operations.typeof_fun [ (f le) ] in 
		Expr.mk_app ctx lit_operations.type_constructor [ res ] 

	| _                     ->
		let msg = Printf.sprintf "Failure - z3 encoding: Unsupported logical expression: %s"
			(JSIL_Print.string_of_logic_expression le false) in
		raise (Failure msg) 



let rec encode_assertion a : Expr.expr =

	(* print_time_debug "EPF:"; *)
	let f = encode_assertion in
	let fe = encode_logical_expression in

	match a with
	| LNot a             -> Boolean.mk_not ctx (f a) 
	| LEq (le1, le2)     -> Boolean.mk_eq ctx (fe le1) (fe le2)
	| LLess (le1, le2)   -> 
		let le1' = Expr.mk_app ctx lit_operations.number_accessor  [ (fe le1) ] in
		let le2' = Expr.mk_app ctx lit_operations.number_accessor  [ (fe le2) ] in
		mk_lt ctx le1' le2' 
	| LLessEq (le1, le2) -> 
		let le1' = Expr.mk_app ctx lit_operations.number_accessor  [ (fe le1) ] in
		let le2' = Expr.mk_app ctx lit_operations.number_accessor  [ (fe le2) ] in
		mk_le ctx le1' le2'
	| LStrLess (_, _)    -> raise (Failure ("Z3 encoding does not support STRLESS"))
	| LTrue	             -> Boolean.mk_true ctx
	| LFalse             -> Boolean.mk_false ctx
	| LOr (a1, a2)       -> Boolean.mk_or ctx [ (f a1); (f a2) ]
	| LAnd (a1, a2)      -> Boolean.mk_and ctx [ (f a1); (f a2) ] 
	| _ ->
		let msg = Printf.sprintf "Unsupported assertion to encode for Z3: %s" (JSIL_Print.string_of_logic_assertion a false) in
		raise (Failure msg)


let encode_assertion_top_level a = encode_assertion (JSIL_Logic_Utils.push_in_negations_off a) 



let encode_quantifier quantifier_type ctx quantified_vars var_sorts assertion =
	if ((List.length quantified_vars) > 0) then
		(let quantified_assertion =
			Quantifier.mk_quantifier
				ctx
				quantifier_type
				(List.map2 (fun v s -> Expr.mk_const_s ctx v s ) quantified_vars var_sorts)
				assertion
				None
				[]
				[]
				None
				None in
		let quantifier_str = Quantifier.to_string quantified_assertion in
		let quantified_assertion = Quantifier.expr_of_quantifier quantified_assertion in
		let quantified_assertion = Expr.simplify quantified_assertion None in
		quantified_assertion)
	else assertion


let make_typeof_axioms lits types = 

	let make_typeof_single_axiom lit l_type = 
		let lit        = encode_lit lit in 
		let l_type     = (encode_type l_type)  in 
		let typeof_lit = Expr.mk_app ctx axiomatised_operations.typeof_fun [ lit ] in 
		Boolean.mk_eq ctx l_type typeof_lit in 

	try List.map2 make_typeof_single_axiom lits types
		with _ -> raise (Failure "DEATH: make_typeof_axioms")


let global_axioms = 
	
	(* forall x. slen(x) >= 0 *)
	let x    = "x" in 
	let le_x = mk_const (mk_string_symb x) in
	let le1  = Expr.mk_app ctx axiomatised_operations.slen_fun [ le_x ] in
	let le2  = mk_num_i 0 in
	let slen_assertion = mk_ge ctx le1 le2 in
	let slen_axiom     = encode_quantifier true ctx [ x ] [ numbers_sort ] slen_assertion in

	(* forall x. llen(x) >= 0 *)
	let x    = "x" in
	let le_x = Expr.mk_const ctx (mk_string_symb x) z3_jsil_list_sort in
	let le1  = Expr.mk_app ctx axiomatised_operations.llen_fun [ le_x ] in
	let le2  = mk_num_i 0 in
	let llen_assertion = mk_ge ctx le1 le2 in
	let llen_axiom1 = encode_quantifier true ctx [ x ] [ z3_jsil_list_sort ] llen_assertion in

	(* forall x. (x = nil) \/ (llen(x) > 0) *)
	let x         = "x" in
	let le_x      = Expr.mk_const ctx (mk_string_symb x) z3_jsil_list_sort in
	let a1        = Boolean.mk_eq ctx le_x (Expr.mk_app ctx lit_operations.nil_constructor []) in
	let le_llen_x = Expr.mk_app ctx axiomatised_operations.llen_fun [ le_x ] in
	let a2        = mk_lt ctx (mk_num_i 0) le_llen_x in
	let a         = Boolean.mk_or ctx [a1; a2] in
	let llen_axiom2 = encode_quantifier true ctx [ x ] [ z3_jsil_list_sort ] a in


	let typeof_axioms = 
		make_typeof_axioms 
			[ Undefined; Null; Empty; (Bool true); (Bool false)]
			[ UndefinedType; NullType; EmptyType; BooleanType; BooleanType ] in 
	[ slen_axiom; llen_axiom1; (* llen_axiom2 *) ] @ typeof_axioms


let encode_gamma gamma = 
	let gamma_var_type_pairs = get_gamma_var_type_pairs gamma in
	let encoded_gamma = 
		List.filter 
			(fun x -> x <> Boolean.mk_true ctx)
			(List.map
				(fun (x, t_x) ->
					if ((is_lvar_name x) || (is_abs_loc_name x))
						then (
							let le_x           = Expr.mk_const ctx (mk_string_symb x) z3_jsil_literal_sort in
							let le_typeof_le_x = Expr.mk_app ctx axiomatised_operations.typeof_fun [ le_x ] in
							let assertion      = Boolean.mk_eq ctx le_typeof_le_x (encode_type t_x) in
							assertion)
						else Boolean.mk_true ctx)
			gamma_var_type_pairs) in
	encoded_gamma

let string_of_z3_expr_list exprs =
	List.fold_left
		(fun ac e ->
			let e_str = Expr.to_string e in
			if (ac = "") then e_str else (ac ^ ",\n" ^ e_str))
		""
		exprs

let get_new_solver assertions gamma =
  	(* let string_axioms = get_them_nasty_string_axioms tr_ctx assertions in *)
	let assertions = List.map encode_assertion_top_level assertions in
	let assertions = global_axioms @ (encode_gamma gamma) @ assertions in
	let solver = (Solver.mk_solver ctx None) in
	Solver.add solver assertions;
	solver

let dispose_solver solver =
	Gc.full_major ();
	Solver.reset solver


let print_model solver =
	let model = Solver.get_model solver in
	match model with
	| Some model ->
		let str_model = Model.to_string model in
		print_endline (Printf.sprintf "I found the model: \n\n%s" str_model)
	| None ->
		print_endline "No model found."

let string_of_solver solver =
	let exprs = Solver.get_assertions solver in
	string_of_z3_expr_list exprs


let make_list_axioms a_list =
	
	let rec loop_nth original_les les i axioms = 
		match les with 
		| []               -> axioms 
		| le :: rest_les   -> 
			let cur_axiom = LEq ((LLstNth (LEList original_les, LLit (Num (float_of_int i)))), le) in 
			loop_nth original_les rest_les (i+1) (cur_axiom :: axioms) in 

	
	match a_list with 
	| LEList les -> 
		let len_axiom  = LEq (LUnOp (LstLen, a_list), LLit (Num (float_of_int (List.length les)))) in 
		let nth_axioms = loop_nth les les 0 [] in 
		len_axiom :: nth_axioms 
	| LBinOp (le_hd, LstCons, le_tail) -> 
		let len_axiom  = LEq (LUnOp (LstLen, a_list), 
							  LBinOp (LLit (Num (float_of_int 1)), Plus, LUnOp (LstLen, le_tail))) in 
	    let nth_axiom  = LEq ((LLstNth (a_list, LLit (Num (float_of_int 0)))), le_hd) in  
	    [ len_axiom; nth_axiom ]
	| _ -> []
	

let make_string_axioms s =
	let explode s =
  		let rec exp i l =
    		if i < 0 then l else exp (i - 1) ((String.make 1 s.[i]) :: l) in
  		exp (String.length s - 1) [] in 

	let rec loop_nth chars i axioms = 
		match chars with 
		| []               -> axioms 
		| c :: rest_chars   -> 
			let cur_axiom = LEq ((LStrNth (LLit (String s), LLit (Num (float_of_int i)))), LLit (String c)) in 
			loop_nth rest_chars (i+1) (cur_axiom :: axioms) in 

	let slen_axiom = LEq (LUnOp (StrLen, (LLit (String s))), LLit (Num (float_of_int (String.length s)))) in 
	slen_axiom :: (loop_nth (explode s) 0 [])


let make_relevant_axioms a = 
	(* string axioms *)
	let a_strings, _ = JSIL_Logic_Utils.get_assertion_string_number_literals a in
	let a_strings    = JSIL_Logic_Utils.remove_string_duplicates a_strings in 
	let s_axioms     = List.concat (List.map make_string_axioms a_strings) in 

	(* list axioms *)
	let a_lists      = JSIL_Logic_Utils.get_assertion_lists a in
	let l_axioms     = List.concat (List.map make_list_axioms a_lists) in 	

	print_debug_petar (Printf.sprintf "Generated List Axioms:\n%s\n"
	   (Symbolic_State_Print.string_of_shallow_p_formulae (DynArray.of_list l_axioms) false));

	s_axioms @ l_axioms 



let check_satisfiability assertions gamma =
	print_debug_petar (Printf.sprintf "Non-simplified:\nPure formulae:\n%s\nGamma:\n%s\n\n"
		(Symbolic_State_Print.string_of_shallow_p_formulae (DynArray.of_list assertions) false)
		(Symbolic_State_Print.string_of_gamma gamma));
	let solver = get_new_solver assertions gamma in
	print_debug_petar (Printf.sprintf "ENT: About to check the following:\n%s" (string_of_solver solver));
	let ret_solver = (Solver.check solver []) in
	let ret = (ret_solver = Solver.SATISFIABLE) in
	ret


let check_entailment (existentials : SS.t) 
					 (left_as      : jsil_logic_assertion list) 
					 (right_as     : jsil_logic_assertion list) 
					 (gamma        : typing_environment) =

	print_time_debug "check_entailment:";	

	print_debug_petar (Printf.sprintf "Preparing entailment check:\nExistentials:\n%s\nLeft:\n%s\nRight:\n%s\nGamma:\n%s\n"
	   (String.concat ", " (SS.elements existentials))
	   (Symbolic_State_Print.string_of_shallow_p_formulae (DynArray.of_list left_as) false)
	   (Symbolic_State_Print.string_of_shallow_p_formulae (DynArray.of_list right_as) false)
	   (Symbolic_State_Print.string_of_gamma gamma));

	(* If right is empty, then the left only needs to be satisfiable *)
	if ((List.length right_as) = 0) then check_satisfiability left_as gamma else
	
	let left_as_axioms = List.concat (List.map make_relevant_axioms left_as) in 
	let left_as = List.map encode_assertion_top_level (left_as_axioms @ left_as) in
	let left_as = global_axioms @ (encode_gamma gamma) @ left_as in	
	let solver = (Solver.mk_solver ctx None) in
	Solver.add solver left_as;
	print_debug_petar (Printf.sprintf "ENT: About to check the following:\n%s" (string_of_solver solver));
	let ret_left = (Solver.check solver [ ]) = Solver.SATISFIABLE in
	if (ret_left) then (
		let right_as_axioms = List.concat (List.map make_relevant_axioms right_as) in 
		let right_as_axioms = List.map encode_assertion_top_level right_as_axioms in
		let right_as = List.map (fun a -> encode_assertion_top_level (LNot a)) right_as in		
		let right_as_or =
			if ((List.length right_as) > 1) then
					(Boolean.mk_or ctx right_as)
				else if ((List.length right_as) = 1) then
					(List.nth right_as 0)
				else Boolean.mk_false ctx in
		
		let existentials = SS.elements existentials in
		let existentials_sorts = List.map (fun _ -> z3_jsil_literal_sort) existentials in 
		let right_as_or =
			if ((List.length existentials) > 0)
				then encode_quantifier true ctx existentials existentials_sorts right_as_or
				else right_as_or in
					
		Solver.add solver (right_as_or :: right_as_axioms);
		print_debug_petar (Printf.sprintf "ENT: About to check the following:\n%s" (string_of_solver solver));
		let ret = (Solver.check solver [ ]) != Solver.SATISFIABLE in
		print_time_debug (Printf.sprintf "check_entailment done: %b. INNER" ret);
		if (not ret) then print_model solver; 
		ret) 
	else (
		print_time_debug "check_entailment done: false. OUTER";
		false) 
	

let is_equal_on_lexprs e1 e2 pfs : bool option = 
(match (e1 = e2) with
| true -> Some (not (e1 = LUnknown))
| false -> (match e1, e2 with

	| LLit (String str), LVar x 
	| LVar x, LLit (String str) ->
		if (String.get str 0 = '@') 
			then if ((List.mem (LNot (LEq (LStrNth (LVar x, LLit (Num 0.)), LLit (String "@")))) pfs)  ||
			         (List.mem (LNot (LEq (LLit (String "@"), LStrNth (LVar x, LLit (Num 0.))))) pfs))
				then Some false 
				else None
			else None

	(* Variables *)
	| PVar x, PVar y 
	| LVar x, LVar y ->
		if (x = y) then Some true else None
	| PVar _, _
	| _, PVar _
	| LVar _, _
	| _, LVar _ -> None
	
	(* Now we have no more variables *)
	
	(* None *)
	| LNone, _
	| _, LNone -> Some false
	(* Literals *)
	| LLit l1, LLit l2 -> Some (l1 = l2)
	(* ALocs *)
	| ALoc a1, ALoc a2 -> Some (a1 = a2)
	| ALoc _, LLit (Loc _) 
	| LLit (Loc _), ALoc _ -> None
	| ALoc _, _
	| _, ALoc _ -> Some false
	(* LELists *)
	| LLit (LList _), LEList _
	| LEList _, LLit (LList _) -> None
	| LLit _, LEList _ 
	| LEList _, LLit _ -> Some false
	
	(* other *)
	| _, _ -> None))

let is_equal e1 e2 pure_formulae (* solver *) gamma =
	let pfs = DynArray.to_list pure_formulae in
	let result = (match (is_equal_on_lexprs e1 e2 pfs) with
		| Some b -> b
		| None ->  check_entailment SS.empty (Symbolic_State.pfs_to_list pure_formulae) [ (LEq (e1, e2)) ] gamma) in
	result


let is_different e1 e2 pure_formulae (* solver *) gamma =
	let pfs = DynArray.to_list pure_formulae in
	let result = (match (is_equal_on_lexprs e1 e2 pfs) with
		| Some b -> not b
		| None -> check_entailment SS.empty (Symbolic_State.pfs_to_list pure_formulae) [ LNot (LEq (e1, e2)) ] gamma) in
	result

