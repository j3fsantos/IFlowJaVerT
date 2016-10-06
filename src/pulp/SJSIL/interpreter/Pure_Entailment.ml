open Z3
open JSIL_Syntax

let evaluate_type_of lit =
	match lit with
	| Undefined    -> UndefinedType
	| Null         -> NullType
	| Empty        -> EmptyType
	| Constant _   -> NumberType
	| Bool _       -> BooleanType
	| Integer _    -> IntType
	| Num n        -> if (n = (snd (modf n))) then IntType else NumberType
	| String _     -> StringType
	| Loc _        -> ObjectType
	| Type _       -> TypeType
	| LVRef (_, _) -> VariableReferenceType
	| LORef (_, _) -> ObjectReferenceType
	| LList _      -> ListType



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


let types_encoded_as_ints = [
	UndefinedType;
	NullType;
	EmptyType;
	NoneType;
	BooleanType;
	IntType;
	StringType;
	ObjectType;
	TypeType
]

type smt_translation_ctx = {
	z3_ctx            : context;
	tr_typing_env     : JSIL_Memory_Model.typing_environment;
	tr_typing_env_aux : JSIL_Memory_Model.typing_environment;
	tr_typeof_fun     : FuncDecl.func_decl;
	tr_llen_fun       : FuncDecl.func_decl;
	tr_slen_fun       : FuncDecl.func_decl;
	tr_num2str_fun    : FuncDecl.func_decl;
	tr_str2num_fun    : FuncDecl.func_decl;
	tr_num2int_fun    : FuncDecl.func_decl;
	tr_lnth_fun       : FuncDecl.func_decl;
	tr_snth_fun       : FuncDecl.func_decl;
  	tr_list_sort      : Sort.sort;
  	tr_list_nil       : FuncDecl.func_decl;
	tr_list_is_nil    : FuncDecl.func_decl;
	tr_list_cons      : FuncDecl.func_decl;
	tr_list_is_cons   : FuncDecl.func_decl;
	tr_list_head      : FuncDecl.func_decl;
	tr_list_tail      : FuncDecl.func_decl;
	tr_axioms         : Expr.expr list
	(* tr_existentials   : string list *)
}

let get_sort tr_ctx var_type =
	let ctx = tr_ctx.z3_ctx in
	match var_type with
	| None                                           -> Arithmetic.Integer.mk_sort ctx
	| Some t when (List.mem t types_encoded_as_ints) -> Arithmetic.Integer.mk_sort ctx
	| Some NumberType                                -> Arithmetic.Real.mk_sort ctx
	| Some ListType                                  -> tr_ctx.tr_list_sort
	| _  -> raise (Failure "Z3 encoding: Unsupported type.")


let get_z3_var_symbol tr_ctx var = Symbol.mk_string (tr_ctx.z3_ctx) var

let get_sorts tr_ctx vars =
	let gamma = tr_ctx.tr_typing_env in
	List.map (fun x -> let var_type = JSIL_Memory_Model.gamma_get_type gamma x in get_sort tr_ctx var_type) vars

let get_z3_vars tr_ctx vars =
	List.map (fun x -> get_z3_var_symbol tr_ctx x) vars


let encode_quantifier quantifier_type ctx quantified_vars var_sorts assertion =
	if ((List.length quantified_vars) > 0) then
		(let quantified_assertion =
			Quantifier.mk_quantifier
				ctx
				quantifier_type
				(List.map2 (fun v s -> Expr.mk_const_s ctx v s) quantified_vars var_sorts)
				assertion
				None
				[]
				[]
				None
				None in
		let quantifier_str = Quantifier.to_string quantified_assertion in
		(* Printf.printf "Quantified Assertion: %s\n" quantifier_str; *)
		let quantified_assertion = Quantifier.expr_of_quantifier quantified_assertion in
		let quantified_assertion = Expr.simplify quantified_assertion None in
		quantified_assertion)
	else assertion


(* exists x. (typeof(x) == JSIL_Type) : for every JSIL type*)
let mk_typeof_axioms ctx z3_typeof_fun z3_typeof_fun_domain =
	let loop_fun jsil_type =
		(match jsil_type with
		| UndefinedType | NullType | EmptyType | NoneType ->
			let x = "x" in
			let le_x = Arithmetic.Integer.mk_const ctx (Symbol.mk_string ctx x) in
			let le1 = (Expr.mk_app ctx z3_typeof_fun [ le_x ]) in
			let le2 = encode_type ctx jsil_type in
			let typeof_assertion = Boolean.mk_eq ctx le1 le2 in
			let z3_typeof_axiom = encode_quantifier false ctx [ x ] z3_typeof_fun_domain typeof_assertion in
			z3_typeof_axiom
		| _ ->
			let x = "x" in
			let y = "y" in
			let le_x = Arithmetic.Integer.mk_const ctx (Symbol.mk_string ctx x) in
			let le_y = Arithmetic.Integer.mk_const ctx (Symbol.mk_string ctx y) in
			let le11 = (Expr.mk_app ctx z3_typeof_fun [ le_x ]) in
			let le12 =  encode_type ctx jsil_type in
			let le21 = (Expr.mk_app ctx z3_typeof_fun [ le_y ]) in
			let le22=  encode_type ctx jsil_type in
			let typeof_assertion1 = Boolean.mk_eq ctx le11 le12 in
			let typeof_assertion2 = Boolean.mk_eq ctx le21 le22 in
			let typeof_assertion3 = Boolean.mk_not ctx (Boolean.mk_eq ctx le_x le_y) in
			let typeof_assertion = Boolean.mk_and ctx [ typeof_assertion1; typeof_assertion2; typeof_assertion3 ] in
			let type_of_domain = List.nth z3_typeof_fun_domain 0 in
			let z3_typeof_axiom = encode_quantifier false ctx [ x; y ] [ type_of_domain; type_of_domain ] typeof_assertion in
			z3_typeof_axiom) in
	List.map loop_fun [ UndefinedType; NullType; EmptyType; NoneType; BooleanType; IntType; NumberType; StringType; ObjectType; ListType; TypeType]


let mk_smt_translation_ctx gamma existentials =
	let cfg = [("model", "true"); ("proof", "false")] in
	let ctx = (mk_context cfg) in

	let z3_typeof_fun_name = (Symbol.mk_string ctx "typeof") in
	let z3_typeof_fun_domain = [ Arithmetic.Integer.mk_sort ctx ] in
	let z3_typeof_fun = FuncDecl.mk_func_decl ctx z3_typeof_fun_name z3_typeof_fun_domain (Arithmetic.Integer.mk_sort ctx) in
	let z3_typeof_axioms = mk_typeof_axioms ctx z3_typeof_fun z3_typeof_fun_domain in

	let z3_slen_name = (Symbol.mk_string ctx "s-len") in
	let z3_slen_fun_domain = [ Arithmetic.Integer.mk_sort ctx ] in
	let z3_slen_fun = FuncDecl.mk_func_decl ctx z3_slen_name z3_slen_fun_domain (Arithmetic.Integer.mk_sort ctx) in

	(* forall x. slen(x) >= 0 *)
	let x = "x" in
	let le_x = Arithmetic.Integer.mk_const ctx (Symbol.mk_string ctx x) in
	let le1 = (Expr.mk_app ctx z3_slen_fun [ le_x ]) in
	let le2 = (Arithmetic.Integer.mk_numeral_i ctx 0) in
	let slen_assertion = Arithmetic.mk_ge ctx le1 le2 in
	let z3_slen_axiom = encode_quantifier true ctx [ x ] z3_slen_fun_domain slen_assertion in

	let z3_num2str_name = (Symbol.mk_string ctx "num2str") in
	let z3_num2str_fun_domain = [ Arithmetic.Integer.mk_sort ctx ] in
	let z3_num2str_fun = FuncDecl.mk_func_decl ctx z3_num2str_name z3_num2str_fun_domain (Arithmetic.Integer.mk_sort ctx) in

	let z3_str2num_name = (Symbol.mk_string ctx "str2num") in
	let z3_str2num_fun_domain = [ Arithmetic.Integer.mk_sort ctx ] in
	let z3_str2num_fun = FuncDecl.mk_func_decl ctx z3_str2num_name z3_str2num_fun_domain (Arithmetic.Integer.mk_sort ctx) in

	let z3_num2int_name = (Symbol.mk_string ctx "num2int") in
	let z3_num2int_fun_domain = [ Arithmetic.Integer.mk_sort ctx ] in
	let z3_num2int_fun = FuncDecl.mk_func_decl ctx z3_num2int_name z3_num2int_fun_domain (Arithmetic.Integer.mk_sort ctx) in

	let z3_snth_name = (Symbol.mk_string ctx "s-nth") in
	let z3_snth_fun_domain = [ Arithmetic.Integer.mk_sort ctx; Arithmetic.Integer.mk_sort ctx ] in
	let z3_snth_fun = FuncDecl.mk_func_decl ctx z3_snth_name z3_snth_fun_domain (Arithmetic.Integer.mk_sort ctx) in

	let z3_list_sort_name = (Symbol.mk_string ctx "tr_list") in
	let list_sort = Z3List.mk_sort ctx z3_list_sort_name (Arithmetic.Integer.mk_sort ctx) in

	let z3_lnth_name = (Symbol.mk_string ctx "l-nth") in
	let z3_lnth_fun_domain = [ list_sort; Arithmetic.Integer.mk_sort ctx ] in
	let z3_lnth_fun = FuncDecl.mk_func_decl ctx z3_lnth_name z3_lnth_fun_domain (Arithmetic.Integer.mk_sort ctx) in

	let z3_llen_name = (Symbol.mk_string ctx "l-len") in
	let z3_llen_fun_domain = [ list_sort ] in
	let z3_llen_fun = FuncDecl.mk_func_decl ctx z3_llen_name z3_llen_fun_domain (Arithmetic.Integer.mk_sort ctx) in

	(* forall x. slen(x) >= 0 *)
	let x = "x" in
	let le_x = Arithmetic.Integer.mk_const ctx (Symbol.mk_string ctx x) in
	let le1 = (Expr.mk_app ctx z3_slen_fun [ le_x ]) in
	let le2 = (Arithmetic.Integer.mk_numeral_i ctx 0) in
	let slen_assertion = Arithmetic.mk_ge ctx le1 le2 in
	let z3_slen_axiom = encode_quantifier true ctx [ x ] z3_slen_fun_domain slen_assertion in

	(* Printf.printf "After slen!\n"; *)

	(* forall x. llen(x) >= 0 *)
	let x = "x" in
	let le_x = (Expr.mk_const ctx (Symbol.mk_string ctx x) list_sort) in
	let le1 = (Expr.mk_app ctx z3_llen_fun [ le_x ]) in
	let le2 = (Arithmetic.Integer.mk_numeral_i ctx 0) in
	let llen_assertion = Arithmetic.mk_ge ctx le1 le2 in
	let z3_llen_axiom = encode_quantifier true ctx [ x ] z3_llen_fun_domain llen_assertion in

	(* Printf.printf "After llen!\n"; *)

	let list_nil     = Z3List.get_nil_decl     list_sort in
	let list_is_nil  = Z3List.get_is_nil_decl  list_sort in
	let list_cons    = Z3List.get_cons_decl    list_sort in
	let list_is_cons = Z3List.get_is_cons_decl list_sort in
	let list_head    = Z3List.get_head_decl    list_sort in
	let list_tail    = Z3List.get_tail_decl    list_sort in

	{
		z3_ctx            = ctx;
		tr_typing_env     = gamma;
		tr_typing_env_aux = JSIL_Memory_Model.mk_gamma ();
		tr_typeof_fun     = z3_typeof_fun;
		tr_slen_fun       = z3_slen_fun;
		tr_llen_fun       = z3_llen_fun;
		tr_num2str_fun    = z3_num2str_fun;
		tr_str2num_fun    = z3_str2num_fun;
		tr_num2int_fun    = z3_num2int_fun;
		tr_snth_fun       = z3_snth_fun;
		tr_lnth_fun       = z3_lnth_fun;
  		tr_list_sort      = list_sort;
 		tr_list_nil       = list_nil;
		tr_list_is_nil    = list_is_nil;
		tr_list_cons      = list_cons;
		tr_list_is_cons   = list_is_cons;
		tr_list_head      = list_head;
		tr_list_tail      = list_tail;
		tr_axioms         = [ z3_slen_axiom; z3_llen_axiom ]
		(* tr_existentials   = existentials *)
	}


let mk_z3_list les tr_ctx =
	let empty_list = Expr.mk_app tr_ctx.z3_ctx tr_ctx.tr_list_nil [ ] in
	let rec loop les cur_list =
		match les with
		| [] -> cur_list
		| le :: rest_les ->
			let new_cur_list = Expr.mk_app tr_ctx.z3_ctx tr_ctx.tr_list_cons [ le; cur_list ] in
			loop rest_les new_cur_list in
	loop les empty_list


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
let rec encode_literal tr_ctx lit =
	let f = encode_literal tr_ctx in
	let ctx = tr_ctx.z3_ctx in
	let gamma = tr_ctx.tr_typing_env in
	match lit with
	| Undefined     -> (Arithmetic.Integer.mk_numeral_i ctx 0), (encode_type ctx UndefinedType)
	| Null          -> (Arithmetic.Integer.mk_numeral_i ctx 1), (encode_type ctx NullType)
	| Empty         -> (Arithmetic.Integer.mk_numeral_i ctx 2), (encode_type ctx EmptyType)
	| Constant c    -> encode_constant ctx c
	| Bool b        ->
		(match b with
		| true        -> (Arithmetic.Integer.mk_numeral_i ctx 0), (encode_type ctx BooleanType)
		| false       -> (Arithmetic.Integer.mk_numeral_i ctx 1), (encode_type ctx BooleanType))
	| Integer i     -> (Arithmetic.Integer.mk_numeral_i ctx i), (encode_type ctx IntType)
	| Num n         ->
		if (n = (snd (modf n)))
			then        (Arithmetic.Integer.mk_numeral_i ctx (int_of_float n)), (encode_type ctx IntType)
			else        (Arithmetic.Real.mk_numeral_s ctx (string_of_float n)), (encode_type ctx NumberType)
	| String s      -> (encode_string ctx s), (encode_type ctx StringType)
	| Loc l         -> (encode_string ctx ("$l" ^ l)), (encode_type ctx ObjectType)
	| Type t        -> (encode_type ctx t), (encode_type ctx TypeType)
	| LList lits ->
		let les_tes = List.map f lits in
		let les, tes =
			List.fold_left
				(fun (les, tes) (le, te) -> (le :: les, te :: tes))
				([], [])
				les_tes in
		let le_list = mk_z3_list les tr_ctx in
		le_list,  (encode_type ctx ListType)

	| _             -> raise (Failure "SMT encoding: Construct not supported yet - literal!")

(** Encode JSIL binary operators *)
let encode_binop tr_ctx op le1 le2 =
	let ctx = tr_ctx.z3_ctx in
	match op with
	| Plus          -> (Arithmetic.mk_add ctx [ le1; le2 ])
	| Minus         -> (Arithmetic.mk_sub ctx [ le1; le2 ])
	| Times         -> (Arithmetic.mk_mul ctx [ le1; le2 ])
	| Div           -> (Arithmetic.mk_div ctx le1 le2)
	| Mod           -> (Arithmetic.Integer.mk_mod ctx le1 le2)
	| LstCons       -> (Expr.mk_app tr_ctx.z3_ctx tr_ctx.tr_list_cons [ le1; le2 ])
	| _     ->
		let msg = Printf.sprintf "SMT encoding: Construct not supported yet - binop - %s!" (JSIL_Print.string_of_binop op) in
		raise (Failure msg)

(** Encode JSIL unary operators *)
let encode_unop tr_ctx op le te =
	(* Printf.printf "Inside encode_unop\n"; *)
	let ctx = tr_ctx.z3_ctx in
	match op with
	| UnaryMinus ->
		let new_le = (Arithmetic.mk_unary_minus ctx le) in
		new_le, te
	| LstLen     ->
			Printf.printf "Inside encode_unop - lstlen. le: %s. te: %s\n" (Expr.to_string le)  (Expr.to_string te);
			(try
				(let new_le = (Expr.mk_app tr_ctx.z3_ctx tr_ctx.tr_llen_fun [ le ]) in
				new_le, (encode_type ctx IntType))
			with _ ->
				(Printf.printf "The error is where we expected it to be!!\n";
				raise (Failure "I am not myself tonight!!\n")))
	| StrLen     ->
		let new_le = (Expr.mk_app tr_ctx.z3_ctx tr_ctx.tr_slen_fun [ le ]) in
		new_le, (encode_type ctx IntType)
	| ToStringOp ->
		let new_le = (Expr.mk_app tr_ctx.z3_ctx tr_ctx.tr_num2str_fun [ le ]) in
		new_le, (encode_type ctx StringType)
	| ToNumberOp ->
		let new_le = (Expr.mk_app tr_ctx.z3_ctx tr_ctx.tr_str2num_fun [ le ]) in
		new_le, (encode_type ctx NumberType)
	| ToIntOp    ->
		let new_le = (Expr.mk_app tr_ctx.z3_ctx tr_ctx.tr_num2int_fun [ le ]) in
		new_le, (encode_type ctx IntType)
	| _          ->
		Printf.printf "SMT encoding: Construct not supported yet - unop - %s!\n" (JSIL_Print.string_of_unop op);
		let msg = Printf.sprintf "SMT encoding: Construct not supported yet - unop - %s!" (JSIL_Print.string_of_unop op) in
		raise (Failure msg)


let get_z3_var_and_type tr_ctx var =
	let ctx = tr_ctx.z3_ctx in
	let gamma = tr_ctx.tr_typing_env in
	let var_type = JSIL_Memory_Model.gamma_get_type gamma var in
	let var_type_aux = JSIL_Memory_Model.gamma_get_type (tr_ctx.tr_typing_env_aux) var in
	let le, te =
		(match var_type, var_type_aux with
		  | None, None ->
				let le = (Arithmetic.Integer.mk_const ctx (Symbol.mk_string ctx var)) in
		    le, (Expr.mk_app ctx tr_ctx.tr_typeof_fun [ le ])
		  | Some t, _
			| None, Some t when (List.mem t types_encoded_as_ints) ->
				(Arithmetic.Integer.mk_const ctx (Symbol.mk_string ctx var)), (encode_type ctx t)
			| Some ListType, _
			| _, Some ListType ->
				(Expr.mk_const ctx (Symbol.mk_string ctx var) tr_ctx.tr_list_sort), (encode_type ctx ListType)
			| Some NumberType, _
			| _, Some NumberType ->
				(Arithmetic.Real.mk_const ctx (Symbol.mk_string ctx var)), (encode_type ctx NumberType)
			| _               -> raise (Failure "z3 variable encoding: fatal error")) in
	le, te


(** Encode JSIL logical expressions *)
let rec encode_logical_expression tr_ctx e =
	(* Printf.printf "Inside encode logical expression\n"; *)
	let ele = encode_logical_expression tr_ctx in
	let ctx = tr_ctx.z3_ctx in
	let gamma = tr_ctx.tr_typing_env in

	(match e with
	| LLit lit              ->
		let le, te = encode_literal tr_ctx lit in
		le, te, []

	| LNone                 ->
		let le, te = (Arithmetic.Integer.mk_numeral_i ctx 3), (encode_type ctx NoneType) in
		le, te, []

	| LVar var
	| ALoc var              ->
		let le, te = get_z3_var_and_type tr_ctx var in
		le, te, []

	| PVar _                -> raise (Failure "Program variable in pure formula: FIRE")

	| LBinOp (le1, op, le2) ->
		let le1, te1, as1 = ele le1 in
		let le2, te2, as2 = ele le2 in
		let le = encode_binop tr_ctx op le1 le2 in
		let as_op = Boolean.mk_eq ctx te1 te2 in
		le, te1, (as_op :: (as1 @ as2))

	| LUnOp (op, le)        ->
		(* Printf.printf "Inside encode logical expression - unop\n"; *)
		let le, te, as1 = ele le in
		let le, te      = encode_unop tr_ctx op le te in
		le, te, as1

	| LEList les            ->
		let les_tes_as = List.map ele les in
		let les, tes, assertions =
			List.fold_left
				(fun (les, tes, ac_assertions) (le, te, le_assertions) -> (le :: les, te :: tes, le_assertions @ ac_assertions))
				([], [], [])
				les_tes_as in
		let le_list = mk_z3_list les tr_ctx in
		le_list, (encode_type ctx ListType), assertions

	| LLstNth (lst, index)  ->
		let le_lst, te_lst, as_lst = ele lst in
		let le_index, te_index, as_index = ele index in
		let le_len_lst = (Expr.mk_app ctx tr_ctx.tr_llen_fun [ le_lst ]) in
	 	let constraint_list_type     = Boolean.mk_eq ctx te_lst (encode_type ctx ListType) in
		let constraint_index_type    = Boolean.mk_eq ctx te_index (encode_type ctx IntType) in
		let constraint_valid_index_1 = Arithmetic.mk_lt ctx te_index le_len_lst in
		let constraint_valid_index_2 = Arithmetic.mk_ge ctx te_index (Arithmetic.Integer.mk_numeral_i ctx 0) in
		let assertions = as_lst @ as_index @ [ constraint_list_type; constraint_index_type; constraint_valid_index_1; constraint_valid_index_2 ] in
		let le_lnth = (Expr.mk_app ctx tr_ctx.tr_lnth_fun [ le_lst; le_index ]) in
		(* WE DON'T KNOW THE TYPE HERE! *)
		le_lnth, (encode_type ctx StringType), assertions

	| LStrNth (str, index)  ->
		let le_str, te_str, as_str = ele str in
		let le_index, te_index, as_index = ele index in
		let le_len_str = (Expr.mk_app ctx tr_ctx.tr_slen_fun [ le_str ]) in
	 	let constraint_string_type   = Boolean.mk_eq ctx te_str (encode_type ctx StringType) in
		let constraint_index_type    = Boolean.mk_eq ctx te_index (encode_type ctx IntType) in
		let constraint_valid_index_1 = Arithmetic.mk_lt ctx te_index le_len_str in
		let constraint_valid_index_2 = Arithmetic.mk_ge ctx te_index (Arithmetic.Integer.mk_numeral_i ctx 0) in
		let assertions = as_str @ as_index @ [ constraint_string_type; constraint_index_type; constraint_valid_index_1; constraint_valid_index_2 ] in
		let le_snth = (Expr.mk_app ctx tr_ctx.tr_snth_fun [ le_str; le_index ]) in
		le_snth, (encode_type ctx StringType), assertions

	| _                     ->
		let msg = Printf.sprintf "Failure - z3 encoding: Unsupported logical expression: %s"
			(JSIL_Print.string_of_logic_expression e false) in
		raise (Failure msg))


(*
	| LBinOp			of jsil_logic_expr * bin_op * jsil_logic_expr
	| LUnOp				of unary_op * jsil_logic_expr
	| LEVRef			of jsil_logic_expr * jsil_logic_expr
	| LEORef			of jsil_logic_expr * jsil_logic_expr
	| LBase				of jsil_logic_expr
	| LField			of jsil_logic_expr
	| LTypeOf			of jsil_logic_expr
	| LEList      of jsil_logic_expr list

	| LStrNth     of jsil_logic_expr * jsil_logic_expr
	| LUnknown *)

let get_solver tr_ctx existentials left_as right_as_or =

		 (* Printf.printf "Left ass:\n";
			List.iter (fun x -> Printf.printf "\n%s\n" (Expr.to_string x)) left_as;
			Printf.printf "\nRight ass:\n";
			Printf.printf "\n%s\n\n" (Expr.to_string right_as_or); *)

		(*
			Printf.printf "The assertion to check is:\n";
			Printf.printf "\n%s\n\n" (Expr.to_string target_assertion);*)
		(* Printf.printf "----- Creating the solver -----\n\n"; *)

	let right_as_or =
		if ((List.length existentials) > 0)
			then encode_quantifier true tr_ctx.z3_ctx existentials (get_sorts tr_ctx existentials) right_as_or
			else right_as_or in

	let right_as_or =
		Expr.simplify right_as_or None in

	Printf.printf "--- ABOUT TO ENTER THE SOLVER ---\n";
	List.iter (fun expr -> Printf.printf "%s\n" (Expr.to_string expr)) left_as;
	Printf.printf "\nIMPLIES:\n\n";
	Printf.printf "%s\n" (Expr.to_string right_as_or);
	Printf.printf "\nDone printing\n";

	let solver = (Solver.mk_solver tr_ctx.z3_ctx None) in
	Solver.add solver (left_as @ [ right_as_or ]);
	solver

(* right_as must be satisfiable *)
let rec check_entailment existentials left_as right_as gamma =
	Printf.printf "------------------------------\n    Entering entailment\n\n";
	let cfg = [("model", "true"); ("proof", "false")] in

	let tr_ctx = mk_smt_translation_ctx gamma existentials in
	let ctx = tr_ctx.z3_ctx in

	let ret_right = check_satisfiability right_as gamma existentials in
	if (not (ret_right)) then
	begin
		Printf.printf "Right side not satisfiable on its own.\n";
		false
	end
	else
		begin
		Printf.printf "Right side satisfiable on its own.\n";
		try
		(* check if left_as => right_as *)
		let right_as = List.map
				(fun a ->
					(* Printf.printf "I am about to encode a pure formula inside the check_entailment: %s\n" (JSIL_Print.string_of_logic_assertion a false); *)
					let a = encode_pure_formula tr_ctx a in
					(* Printf.printf "Z3 Expression: %s\n" (Expr.to_string a);
					Printf.printf "I encoded a pure formula successfully\n"; *)
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
				(fun a -> encode_pure_formula tr_ctx a)
				left_as in
		let left_as = tr_ctx.tr_axioms @ left_as in



		Printf.printf "\nThe existentials are: ";
		List.iter (fun x -> Printf.printf "%s " x) existentials;
		Printf.printf "\n\n";

		(* SOMETHING HAPPENS HERE! *)
		let solver = get_solver tr_ctx existentials left_as right_as_or in

		let ret = (Solver.check solver []) != Solver.SATISFIABLE in

		(*
		 if (not ret) then
			begin
				let model = Solver.get_model solver in

			(match model with
				| Some model ->
					let str_model = Model.to_string model in
					Printf.printf "I found the model: \n\n%s\n\n" str_model
				| None ->
					Printf.printf "No model filha\n");
			Printf.printf "ret: %s\n" (string_of_bool ret);
			end; *)
		Gc.full_major ();
		Solver.reset solver;
		Printf.printf "Check_entailment. Result %b\n" ret;
		Printf.printf "\n    Exiting entailment\n------------------------------\n\n";
		ret
		with Failure msg -> (* Printf.printf "Esta merda explodiuuuu: %s\n" msg; *) false
		end
and
encode_pure_formula tr_ctx a =
	let f = encode_pure_formula tr_ctx in
	let fe = encode_logical_expression tr_ctx in
	let ctx = tr_ctx.z3_ctx in
	let gamma = tr_ctx.tr_typing_env in
	match a with
	| LNot a             -> Boolean.mk_not ctx (encode_pure_formula tr_ctx a)

	| LEq (le1, le2)     ->
		let t1, _ = normalised_is_typable gamma None le1 in
		let t2, _ = normalised_is_typable gamma None le2 in
		let le1, te1, as1 = fe le1 in
		let le2, te2, as2 = fe le2 in
		(match t1, t2 with
		| Some t1, Some t2 ->
			if (t1 = t2)
				then Boolean.mk_eq ctx le2 le1
				else Boolean.mk_false ctx
		| _, _ ->
		  (* Printf.printf "I AM THERE!!!!!. gamma: %s\n" (JSIL_Memory_Print.string_of_gamma gamma);
			Printf.printf "Type hazard. le1: %s. le2: %s\n" (Expr.to_string le1) (Expr.to_string le2); *)
			let cur_as1 = Boolean.mk_eq ctx le1 le2 in
			let cur_as2 = Boolean.mk_eq ctx te1 te2 in
			Boolean.mk_and ctx ([ cur_as1; cur_as2 ] @ as1 @ as2))

	| LLess (le1', le2')   ->
		(* Printf.printf "LLess: %s %s\n" (JSIL_Print.string_of_logic_expression le1' false) (JSIL_Print.string_of_logic_expression le2' false); *)
		let t1, _ = normalised_is_typable gamma None le1' in
		let t2, _ = normalised_is_typable gamma None le2' in
		(* Printf.printf "I determined the types of the things given to less\n"; *)
		let le1, te1, as1 = fe le1' in
		(* Printf.printf "First one passes.\n"; *)
		let le2, te2, as2 = fe le2' in
		(* Printf.printf "Second one passes\n"; *)
		(match t1, t2 with
		| Some t1, Some t2 ->
			let t = types_lub t1 t2 in
			(match t with
			| Some IntType
			| Some NumberType -> Arithmetic.mk_lt ctx le1 le2
			| _ -> Printf.printf "Coucou!! T'habites dans quelle planete?\n";
				   raise (Failure "Arithmetic operation invoked on non-numeric types"))

    | _, _ ->
			(Printf.printf "LLess Error: %s %s. gamma: %s\n"
				(JSIL_Print.string_of_logic_expression le1' false)
				(JSIL_Print.string_of_logic_expression le2' false)
				(JSIL_Memory_Print.string_of_gamma gamma);
			raise (Failure "Death.")))

	| LLessEq (le1, le2) ->
		let le1, te1, as1 = fe le1 in
		let le2, te2, as2 = fe le2 in
		Arithmetic.mk_le ctx le1 le2

	| LStrLess (_, _)    -> raise (Failure ("I don't know how to do string comparison in Z3"))

	| LTrue              -> Boolean.mk_true ctx

	| LFalse             -> Boolean.mk_false ctx

	| LOr (a1, a2)       -> Boolean.mk_or ctx [ (f a1); (f a2) ]

	| LAnd (a1, a2)      -> Boolean.mk_and ctx [ (f a1); (f a2) ]

	| _                  ->
		let msg = Printf.sprintf "Unsupported assertion to encode for Z3: %s" (JSIL_Print.string_of_logic_assertion a false) in
		raise (Failure msg)
and
check_satisfiability assertions gamma existentials =
	let tr_ctx = mk_smt_translation_ctx gamma existentials in
	try
	let assertions =
		List.map
			(fun a ->
				(* Printf.printf "I am about to check the satisfiablity of: %s\n" (JSIL_Print.string_of_logic_assertion a false); *)
				let a = encode_pure_formula tr_ctx a in
				(* Printf.printf "Z3 Expression: %s\n" (Expr.to_string a); *)
				a)
			assertions in
	let solver = (Solver.mk_solver tr_ctx.z3_ctx None) in
	Solver.add solver assertions;
	let ret = (Solver.check solver []) = Solver.SATISFIABLE in
	Gc.full_major ();
	Solver.reset solver;
	(* Printf.printf "Check_satisfiability. Result %b" ret; *)
	ret
	with _ -> false
and
normalised_is_typable gamma (pfrm : JSIL_Memory_Model.pure_formulae option) nlexpr =
	let f = normalised_is_typable gamma pfrm in
	(* Printf.printf "Calling normalised_is_typable with: %s\n" (JSIL_Print.string_of_logic_expression nlexpr false); *)

	(match nlexpr with
	(* Literals are always typable *)
  | LLit lit -> (Some (evaluate_type_of lit), true)

	(* Variables are typable if in gamma, otherwise no no *)
	| LVar var
	| PVar var -> (try ((Some (Hashtbl.find gamma var), true)) with _ -> (None, false))

	(* Abstract locations are always typable, by construction *)
  | ALoc _ -> (Some ObjectType, true)

  (* If what we're trying to type is typable, we should get a type back.
	   What happens when the type is none, but we know it's typable? *)
	| LTypeOf le ->
		let tle, itle = f le in
		if (itle) then (Some TypeType, true) else (None, false)

	(* If we have 'base' in a normalised expression, this means that
	   the expression we're trying to base is not a reference. It could
		 either be a variable or something non-normalisable further.
		 If it is a variable that has a reference type, we signal that
		 it is typable, but we can't recover the type of the base *)
	| LBase le ->
		(match le with
		| LVar var
		| PVar var ->
			let tvar, itvar = (try ((Some (Hashtbl.find gamma var), true)) with _ -> (None, false)) in
			if (itvar) then
					(match tvar with
					| Some VariableReferenceType
					| Some ObjectReferenceType
					| Some ReferenceType -> (None, true)
					| _ -> (None, false))
				else
					(None, false))

	(* If we have 'field' in a normalised expression, this means that
	   the expression we're trying to field is not a reference. It could
		 either be a variable or something non-normalisable further. If it
		 is a variable that has a string type, we signal that it is typable *)
	| LField le ->
		(match le with
		| LVar var
		| PVar var ->
			let tvar, itvar = (try ((Some (Hashtbl.find gamma var), true)) with _ -> (None, false)) in
			if (itvar) then
					(match tvar with
					| Some StringType -> (Some StringType, true)
					| _ -> (None, false))
				else
					(None, false))

  (* I don't quite understand what happens here when (None, true).
	   LEVRef (E, LBase(y)), where x is a reference whose base
		 has type String but whose type is lost? *)
  | LEVRef (be, fe) ->
		let (bt, ibt) = f be in
		let (ft, ift) = f fe in
		if (ibt && ift) then
			(match ft with
			| Some StringType ->
				(match bt with
				| Some ObjectType
				| Some NumberType
				| Some StringType
				| Some BooleanType
				| Some UndefinedType -> (Some VariableReferenceType, true)
				| _ -> (None, false))
			| _ -> (None, false))
			else
				(None, false)

	(* Same as LEVRef *)
  | LEORef (be, fe) ->
		let (bt, ibt) = f be in
		let (ft, ift) = f fe in
		if (ibt && ift) then
			(match ft with
			| Some StringType ->
				(match bt with
				| Some ObjectType
				| Some NumberType
				| Some StringType
				| Some BooleanType
				| Some UndefinedType -> (Some ObjectReferenceType, true)
				| _ -> (None, false))
			| _ -> (None, false))
			else
				(None, false)

  (* LEList *)
	| LEList le ->
		let all_typable =
			(List.fold_left
				(fun ac elem ->
					let (_, ite) = f elem in
						ac && ite)
				true
				le) in
			if (all_typable) then
				(Some ListType, true)
			else
				(None, false)

  | LUnOp (unop, e) ->
		let (te, ite) = f e in
		let tt t1 t2 =
			(match te with
			| Some te ->
				if (types_leq te t1)
					then (Some t2, true)
					else (None, false)
			| None -> (None, false)) in
		(* Printf.printf "UNOP\n\n\n"; *)
		if (ite) then
  		(match unop with
  		| Not -> tt BooleanType BooleanType
  		| UnaryMinus
  		| BitwiseNot
      | M_sgn
      | M_abs
      | M_acos
      | M_asin
      | M_atan
      | M_ceil
      | M_cos
      | M_exp
      | M_floor
      | M_log
      | M_round
      | M_sin
      | M_sqrt
      | M_tan  -> tt NumberType NumberType
  		| ToIntOp
      | ToUint16Op
      | ToInt32Op
      | ToUint32Op -> tt NumberType IntType
  		| ToStringOp -> tt NumberType StringType
  		| ToNumberOp -> tt StringType NumberType
      | IsPrimitive -> (Some BooleanType, true)
      | Cdr
      | Car -> (None, false)
  		| LstLen -> tt ListType IntType
			| StrLen -> tt StringType IntType) (* CHECK *)
		else
			(None, false)

	| LBinOp (e1, op, e2) ->
		let all_types = [ UndefinedType; NullType; EmptyType; BooleanType; IntType; NumberType; StringType; ObjectType; ReferenceType; ObjectReferenceType; VariableReferenceType; ListType; TypeType ] in
		let (te1, ite1) = f e1 in
		let (te2, ite2) = f e2 in
		let check_valid_type t types ret_type =
			let is_t_in_types = List.exists (fun t_arg -> (t = t_arg)) types in
			if (is_t_in_types) then (Some ret_type, true) else (None, false) in
		(match te1, te2 with
		| (Some t1), (Some t2) ->
			let t = types_lub t1 t2 in
			(*(match t with
			| Some t -> Printf.printf  "I am typing a binop on values of type %s\n" (JSIL_Print.string_of_type t)
			| None -> Printf.printf "I am typing a binop on values of types that cannot be combined");*)
			(match op, t with
			| Equal, (Some t) -> check_valid_type t all_types BooleanType
			| LessThan, (Some t)
			| LessThanEqual, (Some t) -> check_valid_type t [ IntType; NumberType ] BooleanType
			| LessThanString, (Some t) -> check_valid_type t [ StringType ] BooleanType
			| Plus, (Some t)
			| Minus, (Some t)
			| Times, (Some t)
			| Mod, (Some t) -> check_valid_type t [ IntType; NumberType ] t
			| Div, (Some t) -> check_valid_type t [ IntType; NumberType ] NumberType
			| And, (Some t)
			| Or, (Some t) -> check_valid_type t [ BooleanType ] BooleanType
			| BitwiseAnd, (Some t)
			| BitwiseOr, (Some t)
			| BitwiseXor, (Some t)
			| LeftShift, (Some t)
			| SignedRightShift, (Some t)
			| UnsignedRightShift, (Some t)
			| M_atan2, (Some t) -> check_valid_type t [ IntType; NumberType ] NumberType
			| M_pow, (Some t) -> check_valid_type t [ IntType; NumberType ] t
			| Subtype, (Some t) -> check_valid_type t all_types BooleanType
			| LstCons, _ -> check_valid_type t2 [ ListType ] ListType
			| LstCat, (Some t) -> check_valid_type t [ ListType ] ListType
			| StrCat, (Some t) -> check_valid_type t [ StringType ] StringType
			| _, Some t ->
				Printf.printf "op: %s, t: %s"  (JSIL_Print.string_of_binop op) (JSIL_Print.string_of_type t);
				raise (Failure "ERROR")
		 	| _, None ->
				Printf.printf "op: %s, t: none"  (JSIL_Print.string_of_binop op) ;
				raise (Failure "ERROR"))
		| _, _ -> (None, false))

	| LLstNth (lst, index) ->
		Printf.printf "LLstNth in normalised_is_typable!\n";
		Printf.printf "Darling targets: %s and %s\n" (JSIL_Print.string_of_logic_expression lst false) (JSIL_Print.string_of_logic_expression index false);

		let (type_lst, _) = f lst in
		let (type_index, _) = f index in
		(match (type_lst, type_index, pfrm) with
		| Some ListType, Some IntType, Some pfrm ->
			Printf.printf "Types have matched.\n";

			(* I want the shit normalised with respect to the pure part *)
			let simplified = normalise_me_silly pfrm gamma (LLstNth (lst, index)) in
			Printf.printf "Simplified: %s" (JSIL_Print.string_of_logic_expression simplified false);

			if (simplified = LLstNth (lst, index)) then (None, false)
			else (f simplified)
		| _, _, _ -> (None, false))

	| LStrNth (str, index) ->
		Printf.printf "LStrNth in normalised_is_typable!\n";
		Printf.printf "Darling targets: %s and %s\n" (JSIL_Print.string_of_logic_expression str false) (JSIL_Print.string_of_logic_expression index false);

		let (type_str, _) = f str in
		let (type_index, _) = f index in
		(match (type_str, type_index) with
		| Some StringType, Some IntType ->
			let pfrm = (match pfrm with Some pfrm -> pfrm | None -> DynArray.create()) in
			Printf.printf "Types have matched.\n";
			let asrt1 = (LNot (LLess (index, LLit (Integer 0)))) in
			let asrt2 = (LLess (index, LUnOp (StrLen, str))) in
			let entail = (check_entailment [] (JSIL_Memory_Model.pfs_to_list pfrm) [ asrt1; asrt2 ] gamma) in
			Printf.printf "Entailment: %b\n" entail;
			if entail
				then (Some StringType, true)
				else (None, false)
		| Some stype, Some itype ->
			Printf.printf "Something went wrong with the types. %s %s\n\n" (JSIL_Print.string_of_type stype) (JSIL_Print.string_of_type stype); (None, false)
		| Some stype, None ->
			Printf.printf "String type: %s Index not typable.\n\n" (JSIL_Print.string_of_type stype); (None, false)
		| None, Some itype ->
			Printf.printf "String not typable. Index type: %s\n\n" (JSIL_Print.string_of_type itype); (None, false)
		| None, None ->
			Printf.printf "Both string and index not typable. Ew.\n\n"; (None, false))

	| LNone    -> (Some NoneType, true)
  | LUnknown -> (None, false))
and
normalise_me_silly (pure_formulae : JSIL_Memory_Model.pure_formulae) gamma lexpr =
(match lexpr with
	| LLstNth (lst, index) ->
		let lit_lst = subst_to_literal pure_formulae gamma lst in
		let lit_idx = subst_to_literal pure_formulae gamma index in
		Printf.printf "normalise_me_silly: %s %s\n" (JSIL_Print.string_of_logic_expression lit_lst false) (JSIL_Print.string_of_logic_expression lit_idx false);
		(match lit_idx with
			| LLit (Num idx) ->
				(match lit_lst with
					| LLit (LList lst) ->
						(try
							let ret = List.nth lst (int_of_float idx) in LLit ret
						with
							| _ -> lexpr)
					| LEList lst ->
						(try
							List.nth lst (int_of_float idx)
						with
							| _ -> lexpr)
					| _ -> lexpr)
			| _ -> lexpr)

	 | _ -> lexpr)
and
subst_to_literal (pure_formulae : JSIL_Memory_Model.pure_formulae) gamma lexpr =
let pf = filter_eqs pure_formulae in
	let rec subst_it pf lexpr =
	(match pf with
	 | LEq (a, b) :: pf ->
	 	let test = (a = lexpr) in
	 		if test then b else (subst_it pf lexpr)
	 | [] -> lexpr
	 | _ -> raise (Failure "NO!")) in
	subst_it pf lexpr
and
filter_eqs (pure_formulae : JSIL_Memory_Model.pure_formulae) =
	DynArray.fold_left
		(fun ac (x : JSIL_Syntax.jsil_logic_assertion) ->
			(match x with
			  | LEq (a, b) -> if ((a = b) || List.mem x ac) then ac else (x :: ac)
			  | _ -> ac)
		) [] pure_formulae

let rec reverse_type_lexpr_aux gamma new_gamma le le_type =
	let f = reverse_type_lexpr_aux gamma new_gamma in
	(* Printf.printf "le: %s\n\n\n" (JSIL_Print.string_of_logic_expression le false); *)
	(match le with
	(* Literals are always typable *)
  | LLit lit -> if ((evaluate_type_of lit) = le_type) then true else false

	(* Variables are reverse-typable if they are already typable *)
	(* with the target type or if they are not typable           *)
	| LVar var
	| PVar var ->
		(match (JSIL_Memory_Model.gamma_get_type gamma var), (JSIL_Memory_Model.gamma_get_type new_gamma var) with
		| Some t, None
		| None, Some t -> if (t = le_type) then true else false
		| None, None -> (JSIL_Memory_Model.update_gamma new_gamma var (Some le_type)); true
		| Some t1, Some t2 -> if (t1 = t2) then true else false)

	(* Abstract locations are reverse-typable if the target type is ObjectType *)
	| ALoc _ -> if (le_type = ObjectType) then true else false

  (* typeof/base/field are not reverse typable because we lose type information *)
	| LTypeOf _
	| LBase _
	| LField _
  | LEVRef (_, _)
  | LEORef (_, _)
	| LEList _ -> false

  | LUnOp (unop, le) ->
		(* Printf.printf "UNOP\n\n\n"; *)
		(match unop with
  	| Not ->
			if (le_type = BooleanType)
				then f le BooleanType
				else false

		| UnaryMinus ->
			if (List.mem le_type [ NumberType; IntType ])
				then f le le_type
				else false

  	| BitwiseNot
    | M_sgn
    | M_abs
    | M_acos
    | M_asin
    | M_atan
    | M_ceil
    | M_cos
    | M_exp
    | M_floor
    | M_log
    | M_round
    | M_sin
    | M_sqrt
    | M_tan
  	| ToIntOp
    | ToUint16Op
    | ToInt32Op
    | ToUint32Op ->
			if (le_type = NumberType)
				then f le le_type
				else false

		| ToStringOp -> false

		| ToNumberOp ->
			if (le_type = StringType)
				then f le NumberType
				else false

	  | IsPrimitive -> false

		| Cdr
    | Car
		| LstLen -> f le ListType

		| StrLen -> f le StringType)


	| LBinOp (le1, op, le2) ->
		(match op with
		| Equal
		| LessThan
		| LessThanEqual -> false
		| LessThanString -> (f le1 StringType) && (f le2 StringType)

		| Plus
		| Minus
		| Times
		| Mod ->
			if ((le_type = NumberType) || (le_type = IntType))
				then ((f le1 le_type) && (f le2 le_type))
				else false

		| Div -> false

		| And
		| Or ->
			if (le_type = BooleanType)
				then ((f le1 BooleanType) && (f le2 BooleanType))
				else false

		| BitwiseAnd
		| BitwiseOr
		| BitwiseXor
		| LeftShift
		| SignedRightShift
		| UnsignedRightShift
		| M_atan2
		| M_pow
		| Subtype
		| LstCons -> false

		| LstCat ->
			if (le_type = ListType)
				then ((f le1 ListType) && (f le2 ListType))
				else false

		| StrCat ->
			if (le_type = StringType)
				then ((f le1 StringType) && (f le2 StringType))
				else false

		| _ ->
			Printf.printf "op: %s, t: %s"  (JSIL_Print.string_of_binop op) (JSIL_Print.string_of_type le_type);
			raise (Failure "ERROR"))

	| LLstNth (le1, le2) -> (f le1 ListType) && (f le2 IntType)

	| LStrNth (le1, le2) -> (f le1 StringType) && (f le2 IntType)

	| LNone    -> (NoneType = le_type)
  | LUnknown -> false)


let reverse_type_lexpr gamma le le_type : JSIL_Memory_Model.typing_environment option =
	let new_gamma : JSIL_Memory_Model.typing_environment = JSIL_Memory_Model.mk_gamma () in
	let ret = reverse_type_lexpr_aux gamma new_gamma le le_type in
	if (ret)
		then Some new_gamma
		else None
