open Z3
open JSIL_Memory_Model
open JSIL_Syntax

let encoding_with_ints = ref false

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

let types_encoded_as_reals = NumberType :: types_encoded_as_ints

(**********************
 * ENCODING-DEPENDENT *
 **********************)

let if_ints x y =
	if (!encoding_with_ints)
		then begin x end
		else begin y end

let mk_sort       = if_ints Arithmetic.Integer.mk_sort      Arithmetic.Real.mk_sort
let mk_const      = if_ints Arithmetic.Integer.mk_const     Arithmetic.Real.mk_const
let mk_num_i      = if_ints Arithmetic.Integer.mk_numeral_i Arithmetic.Real.mk_numeral_i
let encoded_types = if_ints types_encoded_as_ints           types_encoded_as_reals

(* ********************
 * ENCODING-DEPENDENT *
 ********************** *)

(** Encode JSIL type literals as Z3 numerical constants *)
let encode_type ctx jsil_type =
	match jsil_type with
	| UndefinedType         -> mk_num_i ctx 0
	| NullType              -> mk_num_i ctx 1
	| EmptyType             -> mk_num_i ctx 2
	| NoneType              -> mk_num_i ctx 3
	| BooleanType           -> mk_num_i ctx 4
	| IntType               -> mk_num_i ctx 5
	| NumberType            -> mk_num_i ctx 6
	| StringType            -> mk_num_i ctx 7
	| ObjectType            -> mk_num_i ctx 8
	| ListType              -> mk_num_i ctx 12
	| TypeType              -> mk_num_i ctx 13


let get_sort tr_ctx var_type =
	let ctx = tr_ctx.z3_ctx in
	match var_type with
	| None                                   -> mk_sort ctx
	| Some t when (List.mem t encoded_types) -> mk_sort ctx
	| Some ListType                          -> tr_ctx.tr_list_sort
    | Some NumberType                        -> Arithmetic.Real.mk_sort ctx
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
				(List.map2 (fun v s -> Expr.mk_const_s ctx v s ) quantified_vars var_sorts)
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

(* exists x. (typeof(x) == JSIL_Type) : for every JSIL type
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
	List.map loop_fun [ UndefinedType; NullType; EmptyType; NoneType; BooleanType; IntType; NumberType; StringType; ObjectType; ListType; TypeType] *)

let mk_z3_list_core les ctx list_nil list_cons =
	let empty_list = Expr.mk_app ctx list_nil [ ] in
	let rec loop les cur_list =
		match les with
		| [] -> cur_list
		| le :: rest_les ->
			(* Printf.printf "Current: %s\n" (Expr.to_string le); *)
			let new_cur_list = Expr.mk_app ctx list_cons [ le; cur_list ] in
			loop rest_les new_cur_list in
	loop les empty_list


let mk_z3_list les tr_ctx =
	mk_z3_list_core les tr_ctx.z3_ctx tr_ctx.tr_list_nil tr_ctx.tr_list_cons


(*  llen({{ }}) = 0) *)
(* forall a:Any. (llen({{ a }}) = 1) *)
(* forall a:Any, b:Any. (llen({{ a, b }}) = 2) *)
let mk_z3_llen_axioms n ctx list_sort list_len list_nil list_cons =

	(* forall a1: Any, ..., an: Any. (llen{{a1, ..., an}}) = n *)
	let make_llen_axiom n =
		let rec loop n vars le_vars sorts =
			if (n = 0)
				then vars, le_vars, sorts
				else
					(let x = "x_" ^ (string_of_int n) in
					let le_x = Expr.mk_const_s ctx x (mk_sort ctx) in
					loop (n-1) (x :: vars) (le_x :: le_vars) (mk_sort ctx :: sorts)) in
		let vars, le_vars, sorts = loop n [] [] [] in
		let list = mk_z3_list_core le_vars ctx list_nil list_cons in
		let llen_le = (Expr.mk_app ctx list_len [ list ]) in
		let assertion = Boolean.mk_eq ctx (mk_num_i ctx n) llen_le in
		let axiom = encode_quantifier true ctx vars sorts assertion in
	 	axiom in

	let rec loop n axioms =
		let axiom_n = make_llen_axiom n in
		let axioms = axiom_n :: axioms in
		if (n = 0)
			then axioms
			else loop (n - 1) axioms in
	let res = loop n [] in
	res


let mk_smt_translation_ctx gamma existentials =
	let cfg = [("model", "true"); ("proof", "false")] in
	let ctx = (mk_context cfg) in

	let z3_typeof_fun_name = (Symbol.mk_string ctx "typeof") in
	let z3_typeof_fun_domain = [ mk_sort ctx ] in
	let z3_typeof_fun = FuncDecl.mk_func_decl ctx z3_typeof_fun_name z3_typeof_fun_domain (mk_sort ctx) in
	(* let z3_typeof_axioms = mk_typeof_axioms ctx z3_typeof_fun z3_typeof_fun_domain in *)

	let z3_slen_name = (Symbol.mk_string ctx "s-len") in
	let z3_slen_fun_domain = [ mk_sort ctx ] in
	let z3_slen_fun = FuncDecl.mk_func_decl ctx z3_slen_name z3_slen_fun_domain (mk_sort ctx) in

	(* forall x. slen(x) >= 0 *)
	let x = "x" in
	let le_x = mk_const ctx (Symbol.mk_string ctx x) in
	let le1 = (Expr.mk_app ctx z3_slen_fun [ le_x ]) in
	let le2 = (mk_num_i ctx 0) in
	let slen_assertion = Arithmetic.mk_ge ctx le1 le2 in
	let z3_slen_axiom = encode_quantifier true ctx [ x ] z3_slen_fun_domain slen_assertion in

	let z3_num2str_name = (Symbol.mk_string ctx "num2str") in
	let z3_num2str_fun_domain = [ mk_sort ctx ] in
	let z3_num2str_fun = FuncDecl.mk_func_decl ctx z3_num2str_name z3_num2str_fun_domain (mk_sort ctx) in

	let z3_str2num_name = (Symbol.mk_string ctx "str2num") in
	let z3_str2num_fun_domain = [ mk_sort ctx ] in
	let z3_str2num_fun = FuncDecl.mk_func_decl ctx z3_str2num_name z3_str2num_fun_domain (mk_sort ctx) in

	let z3_num2int_name = (Symbol.mk_string ctx "num2int") in
	let z3_num2int_fun_domain = [ mk_sort ctx ] in
	let z3_num2int_fun = FuncDecl.mk_func_decl ctx z3_num2int_name z3_num2int_fun_domain (mk_sort ctx) in

	let z3_snth_name = (Symbol.mk_string ctx "s-nth") in
	let z3_snth_fun_domain = [ mk_sort ctx; mk_sort ctx ] in
	let z3_snth_fun = FuncDecl.mk_func_decl ctx z3_snth_name z3_snth_fun_domain (mk_sort ctx) in

	let z3_list_sort_name = (Symbol.mk_string ctx "tr_list") in
	let list_sort = Z3List.mk_sort ctx z3_list_sort_name (mk_sort ctx) in

	let z3_lnth_name = (Symbol.mk_string ctx "l-nth") in
	let z3_lnth_fun_domain = [ list_sort; mk_sort ctx ] in
	let z3_lnth_fun = FuncDecl.mk_func_decl ctx z3_lnth_name z3_lnth_fun_domain (mk_sort ctx) in

	let z3_llen_name = (Symbol.mk_string ctx "l-len") in
	let z3_llen_fun_domain = [ list_sort ] in
	let z3_llen_fun = FuncDecl.mk_func_decl ctx z3_llen_name z3_llen_fun_domain (mk_sort ctx) in

	let z3_to_jsil_boolean_name = (Symbol.mk_string ctx "to_jsil_boolean") in
	let z3_to_jsil_boolean_domain = [ Boolean.mk_sort ctx ] in
	let z3_to_jsil_boolean_fun = FuncDecl.mk_func_decl ctx z3_to_jsil_boolean_name z3_to_jsil_boolean_domain (mk_sort ctx) in

	let z3_jsil_not_name = (Symbol.mk_string ctx "jsil_not") in
	let z3_jsil_not_domain = [ mk_sort ctx ] in
	let z3_jsil_not_fun : FuncDecl.func_decl = FuncDecl.mk_func_decl ctx z3_jsil_not_name z3_jsil_not_domain (mk_sort ctx) in

	(* to_jsil_boolean axioms *)
	(* to_jsil_boolean true = 1 *)
	(* to_jsil_boolean false = 0 *)
	let to_jsil_boolean_axiom_true = Boolean.mk_eq ctx (Expr.mk_app ctx z3_to_jsil_boolean_fun [ (Boolean.mk_true ctx) ]) (mk_num_i ctx 1)  in
	let to_jsil_boolean_axiom_false = Boolean.mk_eq ctx (Expr.mk_app ctx z3_to_jsil_boolean_fun [ (Boolean.mk_false ctx) ]) (mk_num_i ctx 0) in

	let jsil_not_axiom_true : Z3.Expr.expr = Boolean.mk_eq ctx (Expr.mk_app ctx z3_jsil_not_fun [ (mk_num_i ctx 1) ]) (mk_num_i ctx 0) in
	let jsil_not_axiom_false :  Z3.Expr.expr = Boolean.mk_eq ctx (Expr.mk_app ctx z3_jsil_not_fun [ (mk_num_i ctx 0) ]) (mk_num_i ctx 1) in

	(* forall x. slen(x) >= 0 *)
	let x = "x" in
	let le_x = mk_const ctx (Symbol.mk_string ctx x) in
	let le1 = (Expr.mk_app ctx z3_slen_fun [ le_x ]) in
	let le2 = (mk_num_i ctx 0) in
	let slen_assertion = Arithmetic.mk_ge ctx le1 le2 in
	let z3_slen_axiom = encode_quantifier true ctx [ x ] z3_slen_fun_domain slen_assertion in

	let list_nil     = Z3List.get_nil_decl     list_sort in
	let list_is_nil  = Z3List.get_is_nil_decl  list_sort in
	let list_cons    = Z3List.get_cons_decl    list_sort in
	let list_is_cons = Z3List.get_is_cons_decl list_sort in
	let list_head    = Z3List.get_head_decl    list_sort in
	let list_tail    = Z3List.get_tail_decl    list_sort in

	(* TODO: lub_domain is 0..13, not all ints. Deadline: 2020 *)
	let z3_lub_name = (Symbol.mk_string ctx "type_lub") in
	let z3_lub_domain = [ mk_sort ctx; mk_sort ctx ] in
	let z3_lub = FuncDecl.mk_func_decl ctx z3_lub_name z3_lub_domain (mk_sort ctx) in

  (* forall x, lub x x = x *)
  let x = "x" in
	let le_x = mk_const ctx (Symbol.mk_string ctx x) in
	let le1 = (Expr.mk_app ctx z3_lub [ le_x; le_x ]) in
	let lub_refl_ass = Boolean.mk_eq ctx le1 le_x in
	let lub_refl_axiom = encode_quantifier true ctx [ x ] [ mk_sort ctx ] lub_refl_ass in

  (* forall x, lub x y = lub y x *)
  let x = "x" in
	let le_x = mk_const ctx (Symbol.mk_string ctx x) in
  let y = "y" in
	let le_y = mk_const ctx (Symbol.mk_string ctx y) in
	let le1 = (Expr.mk_app ctx z3_lub [ le_x; le_y ]) in
	let le2 = (Expr.mk_app ctx z3_lub [ le_y; le_x ]) in
	let lub_sym_ass = Boolean.mk_eq ctx le1 le2 in
	let lub_sym_axiom = encode_quantifier true ctx [ x ] [ mk_sort ctx ] lub_sym_ass in

  (* lub Int Num = Num *)
	let it = encode_type ctx IntType in
	let nt = encode_type ctx NumberType in
	let le1 = (Expr.mk_app ctx z3_lub [ it; nt ]) in
	let lub_int_num_axiom = Boolean.mk_eq ctx le1 nt in
	let le2 = (Expr.mk_app ctx z3_lub [ nt; it ]) in
	let lub_num_int_axiom = Boolean.mk_eq ctx le2 nt in

	(* forall x. llen(x) >= 0 *)
	let x = "x" in
	let le_x = (Expr.mk_const ctx (Symbol.mk_string ctx x) list_sort) in
	let le1 = (Expr.mk_app ctx z3_llen_fun [ le_x ]) in
	let le2 = (mk_num_i ctx 0) in
	let llen_assertion = Arithmetic.mk_ge ctx le1 le2 in
	let z3_llen_axiom1 = encode_quantifier true ctx [ x ] z3_llen_fun_domain llen_assertion in

	(* forall x. (x = nil) \/ (llen(x) > 0) *)
    let x = "x" in
	let le_x = (Expr.mk_const ctx (Symbol.mk_string ctx x) list_sort) in
	let ass1 = Boolean.mk_eq ctx le_x (Expr.mk_app ctx list_nil [ ]) in
	let le_llen_x = (Expr.mk_app ctx z3_llen_fun [ le_x ]) in
	let ass2 = Arithmetic.mk_lt ctx (mk_num_i ctx 0) le_llen_x in
	let ass = Boolean.mk_or ctx [ass1; ass2] in
	let axiom_llen_axiom2 = encode_quantifier true ctx [ x ] [ list_sort ] ass in

	let llen_axioms = mk_z3_llen_axioms 0 ctx list_sort z3_llen_fun list_nil list_cons in

	{
		z3_ctx                  = ctx;
		tr_typing_env           = gamma;
		tr_typeof_fun           = z3_typeof_fun;
		tr_slen_fun             = z3_slen_fun;
		tr_llen_fun             = z3_llen_fun;
		tr_num2str_fun          = z3_num2str_fun;
		tr_str2num_fun          = z3_str2num_fun;
		tr_num2int_fun          = z3_num2int_fun;
		tr_snth_fun             = z3_snth_fun;
		tr_lnth_fun             = z3_lnth_fun;
  		tr_list_sort            = list_sort;
 		tr_list_nil             = list_nil;
		tr_list_is_nil          = list_is_nil;
		tr_list_cons            = list_cons;
		tr_list_is_cons         = list_is_cons;
		tr_list_head            = list_head;
		tr_list_tail            = list_tail;
		tr_lub                  = z3_lub;
		tr_to_jsil_boolean_fun  = z3_to_jsil_boolean_fun;
		tr_jsil_not_fun         = z3_jsil_not_fun;
		tr_axioms               = [ z3_slen_axiom;
		                            z3_llen_axiom1;
									lub_refl_axiom;
									lub_int_num_axiom;
									lub_num_int_axiom;
									axiom_llen_axiom2;
									to_jsil_boolean_axiom_true;
									to_jsil_boolean_axiom_false;
									jsil_not_axiom_true;
									jsil_not_axiom_false ] @ llen_axioms
		(* tr_existentials   = existentials *)
	}


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
		let z3_code = mk_num_i ctx str_number in
		z3_code
	with Not_found ->
		(* New string: add it to the hashtable *)
		let z3_code = mk_num_i ctx !str_counter in
		Hashtbl.add str_codes str (!str_counter);
		str_counter := !str_counter + 1;
		z3_code


(** Encode JSIL literals as Z3 numerical constants *)
let rec encode_literal tr_ctx lit =
	(* Printf.printf "    EL: %s\n" (JSIL_Print.string_of_literal lit false); *)
	let f = encode_literal tr_ctx in
	let ctx = tr_ctx.z3_ctx in
	let gamma = tr_ctx.tr_typing_env in
	match lit with
	| Undefined     -> (mk_num_i ctx 0), (encode_type ctx UndefinedType)
	| Null          -> (mk_num_i ctx 1), (encode_type ctx NullType)
	| Empty         -> (mk_num_i ctx 2), (encode_type ctx EmptyType)
	| Constant c    -> encode_constant ctx c
	| Bool b        ->
		(match b with
		| true      -> (mk_num_i ctx 1), (encode_type ctx BooleanType)
		| false     -> (mk_num_i ctx 0), (encode_type ctx BooleanType))
	| Integer i     -> (mk_num_i ctx i), (encode_type ctx IntType)
	| Num n         ->
		if (n = (snd (modf n)))
			then       (mk_num_i ctx (int_of_float n)), (encode_type ctx IntType)
			else       (Arithmetic.Real.mk_numeral_s ctx (string_of_float n)), (encode_type ctx NumberType)
	| String s      -> (encode_string ctx s), (encode_type ctx StringType)
	| Loc l         -> (encode_string ctx ("$l" ^ l)), (encode_type ctx ObjectType)
	| Type t        -> (encode_type ctx t), (encode_type ctx TypeType)
	| LList lits ->
		(* Printf.printf "    Creating literal list.\n"; *)
		let les_tes = List.map f lits in
		let les, tes =
			List.fold_left
				(fun (les, tes) (le, te) -> (le :: les, te :: tes))
				([], [])
				les_tes in
		let le_list = mk_z3_list les tr_ctx in
		(* Printf.printf ("    Created literal list.\n"); *)
		le_list,  (encode_type ctx ListType)

	| _             -> raise (Failure "SMT encoding: Construct not supported yet - literal!")


let mk_constraint_int_num_or tr_ctx te =
	let ctx = tr_ctx.z3_ctx in
	let as_op_1 = Boolean.mk_eq ctx te (encode_type ctx NumberType) in
	let as_op_2 = Boolean.mk_eq ctx te (encode_type ctx IntType) in
	let as_op   = Boolean.mk_or ctx [ as_op_1; as_op_2 ] in
	as_op


let mk_constraint_int_num tr_ctx te1 te2 =
	let ctx = tr_ctx.z3_ctx in
	let as_op_1 = mk_constraint_int_num_or tr_ctx te1 in
	let as_op_2 = mk_constraint_int_num_or tr_ctx te2 in
	let as_op   = Boolean.mk_and ctx [ as_op_1; as_op_2 ] in
	as_op


let mk_constraint_int tr_ctx te1 te2 =
	let ctx = tr_ctx.z3_ctx in
	let as_op_1 = Boolean.mk_eq  ctx te1 (encode_type ctx IntType) in
	let as_op_2 = Boolean.mk_eq  ctx te2 (encode_type ctx IntType) in
	let as_op   = Boolean.mk_and ctx [ as_op_1; as_op_2 ] in
	as_op


let mk_constraint_type tr_ctx te t =
	let ctx = tr_ctx.z3_ctx in
	let as_op = Boolean.mk_eq ctx te (encode_type ctx t) in
	as_op


let mk_lub_type tr_ctx t1 t2 =
	let ctx = tr_ctx.z3_ctx in
	(Expr.mk_app ctx tr_ctx.tr_lub [ t1; t2 ])


(** Encode JSIL binary operators *)
let encode_binop tr_ctx op le1 te1 le2 te2 =
	let ctx = tr_ctx.z3_ctx in

	match op with
	| Plus     -> (Arithmetic.mk_add ctx [ le1; le2 ]), mk_lub_type tr_ctx te1 te2, [ mk_constraint_int_num tr_ctx te1 te2 ]
	| Minus    -> (Arithmetic.mk_sub ctx [ le1; le2 ]), mk_lub_type tr_ctx te1 te2, [ mk_constraint_int_num tr_ctx te1 te2 ]
	| Times    -> (Arithmetic.mk_mul ctx [ le1; le2 ]), mk_lub_type tr_ctx te1 te2, [ mk_constraint_int_num tr_ctx te1 te2 ]
	| Div      -> (Arithmetic.mk_div ctx   le1  le2),   mk_lub_type tr_ctx te1 te2, [ mk_constraint_int_num tr_ctx te1 te2 ]
	| Equal    ->
		let new_le = (Expr.mk_app tr_ctx.z3_ctx tr_ctx.tr_to_jsil_boolean_fun [ (Boolean.mk_eq ctx le1 le2) ]) in
		new_le, (encode_type ctx BooleanType), [ ]
	| LstCons  ->
		(* print_endline (Printf.sprintf "So, Bananas...\n (%s : %s) (%s : %s)" (Expr.to_string le1) (Expr.to_string te1) (Expr.to_string le2) (Expr.to_string te2)); *)
		let le, te, constraints = (Expr.mk_app ctx tr_ctx.tr_list_cons [ le1; le2 ]), (encode_type ctx ListType), [ mk_constraint_type tr_ctx te2 ListType] in
		le, te, constraints
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
		new_le, te, [ mk_constraint_int_num_or tr_ctx te ]

	| LstLen ->
		let new_le = (Expr.mk_app tr_ctx.z3_ctx tr_ctx.tr_llen_fun [ le ]) in
		new_le, (encode_type ctx IntType), [ mk_constraint_type tr_ctx te ListType ]

	| StrLen ->
		let new_le = (Expr.mk_app tr_ctx.z3_ctx tr_ctx.tr_slen_fun [ le ]) in
		new_le, (encode_type ctx IntType), [ mk_constraint_type tr_ctx te StringType ]

	| ToStringOp ->
		let new_le = (Expr.mk_app tr_ctx.z3_ctx tr_ctx.tr_num2str_fun [ le ]) in
		new_le, (encode_type ctx StringType), [ mk_constraint_int_num_or tr_ctx te ]

	| ToNumberOp ->
		let new_le = (Expr.mk_app tr_ctx.z3_ctx tr_ctx.tr_str2num_fun [ le ]) in
		new_le, (encode_type ctx NumberType), [ mk_constraint_type tr_ctx te StringType ]

	| ToIntOp ->
		let new_le = (Expr.mk_app tr_ctx.z3_ctx tr_ctx.tr_num2int_fun [ le ]) in
		new_le, (encode_type ctx IntType), [ mk_constraint_type tr_ctx te NumberType ]

	| Not ->
		let new_le = (Expr.mk_app tr_ctx.z3_ctx tr_ctx.tr_jsil_not_fun [  le ]) in
		new_le, (encode_type ctx BooleanType), [ mk_constraint_type tr_ctx te BooleanType ]

	| _          ->
		Printf.printf "SMT encoding: Construct not supported yet - unop - %s!\n" (JSIL_Print.string_of_unop op);
		let msg = Printf.sprintf "SMT encoding: Construct not supported yet - unop - %s!" (JSIL_Print.string_of_unop op) in
		raise (Failure msg)


let get_z3_var_and_type tr_ctx var =
	let ctx = tr_ctx.z3_ctx in
	let gamma = tr_ctx.tr_typing_env in
	let var_type = JSIL_Memory_Model.gamma_get_type gamma var in
	let le, te =
		(match var_type with
			| None            -> let le = (mk_const ctx (Symbol.mk_string ctx var)) in
									le, (Expr.mk_app ctx tr_ctx.tr_typeof_fun [ le ])
			| Some ListType                          -> (Expr.mk_const ctx (Symbol.mk_string ctx var) tr_ctx.tr_list_sort), (encode_type ctx ListType)
			| Some t when (List.mem t encoded_types) -> (mk_const ctx (Symbol.mk_string ctx var)), (encode_type ctx t)
			| Some NumberType                        -> (Arithmetic.Real.mk_const ctx (Symbol.mk_string ctx var)), (encode_type ctx NumberType)
			| _                                      -> raise (Failure "z3 variable encoding: fatal error")) in
	le, te


(** Encode JSIL logical expressions *)
let rec encode_logical_expression tr_ctx e =
	(* Printf.printf "  ELE: %s\n" (JSIL_Print.string_of_logic_expression e false); *)
	let ele = encode_logical_expression tr_ctx in
	let ctx = tr_ctx.z3_ctx in
	let gamma = tr_ctx.tr_typing_env in

	(match e with
	| LLit lit              ->
		let le, te = encode_literal tr_ctx lit in
		le, te, []

	| LNone                 ->
		let le, te = (mk_num_i ctx 3), (encode_type ctx NoneType) in
		le, te, []

	| LVar var ->
		let le, te = get_z3_var_and_type tr_ctx var in
		le, te, []

	| ALoc var ->
		let le = (mk_const ctx (Symbol.mk_string ctx var)) in
			le, (encode_type ctx ObjectType), []

	| PVar _                -> raise (Failure "Program variable in pure formula: FIRE")

	| LBinOp (le1, op, le2) ->
		let le1, te1, as1 = ele le1 in
		let le2, te2, as2 = ele le2 in
		let le, te, new_as = encode_binop tr_ctx op le1 te1 le2 te2 in
		le, te, (new_as @ as1 @ as2)

	| LUnOp (op, le)        ->
		(* Printf.printf "Inside encode logical expression - unop\n"; *)
		let le, te, as1    = ele le in
		let le, te, new_as = encode_unop tr_ctx op le te in
		le, te, new_as @ as1

	| LEList les ->
		(* List.iter (fun x -> Printf.printf "%s " (JSIL_Print.string_of_logic_expression x false)) les; *)
		(* Printf.printf "\n"; *)
		let les_tes_as = List.map ele les in
		let les, tes, assertions =
			List.fold_left
				(fun (les, tes, ac_assertions) (le, te, le_assertions) -> (le :: les, te :: tes, le_assertions @ ac_assertions))
				([], [], [])
				les_tes_as in
		let le_list =
			(* Printf.printf "LEList: encoded : ";
			List.iter (fun x -> Printf.printf "%s " (Expr.to_string x)) les;
			Printf.printf "\n"; *)
			let res = mk_z3_list les tr_ctx in
			res in
		le_list, (encode_type ctx ListType), assertions

	| LLstNth (lst, index)  ->
		let le_lst, te_lst, as_lst       = ele lst in
		let le_index, te_index, as_index = ele index in
		let le_len_lst                   = (Expr.mk_app ctx tr_ctx.tr_llen_fun [ le_lst ]) in
	 	let constraint_list_type         = Boolean.mk_eq ctx te_lst (encode_type ctx ListType) in
		let constraint_index_type        = Boolean.mk_eq ctx te_index (encode_type ctx IntType) in
		let assertions                   = [ constraint_list_type; constraint_index_type ] @ as_lst @ as_index in
		let le_lnth                      = (Expr.mk_app ctx tr_ctx.tr_lnth_fun [ le_lst; le_index ]) in
		le_lnth, (Expr.mk_app ctx tr_ctx.tr_typeof_fun [ le_lnth ]), assertions

	| LStrNth (str, index)  ->
		let le_str, te_str, as_str = ele str in
		let le_index, te_index, as_index = ele index in
	 	let constraint_string_type       = Boolean.mk_eq ctx te_str (encode_type ctx StringType) in
		let constraint_index_type        = Boolean.mk_eq ctx te_index (encode_type ctx IntType) in
		let assertions = [ constraint_string_type; constraint_index_type ] @ as_str @ as_index in
		let le_snth = (Expr.mk_app ctx tr_ctx.tr_snth_fun [ le_str; le_index ]) in
		le_snth, (encode_type ctx StringType), assertions

	| _                     ->
		let msg = Printf.sprintf "Failure - z3 encoding: Unsupported logical expression: %s"
			(JSIL_Print.string_of_logic_expression e false) in
		raise (Failure msg))



(* TODO : Unify the two below *)

let encode_lnth_equalities tr_ctx le_list (les : jsil_logic_expr) =
	let ctx = tr_ctx.z3_ctx in
	let aux (les : jsil_logic_expr list) =
		List.mapi
			(fun i le ->
				let le', _, _ = encode_logical_expression tr_ctx le in
				let le_nth = (Expr.mk_app ctx tr_ctx.tr_lnth_fun [ le_list; (mk_num_i ctx i) ]) in
				Boolean.mk_eq ctx le_nth le')
			les in

	let ctx = tr_ctx.z3_ctx in
	match les with
	| LLit (LList l) -> aux (List.map (fun (v : jsil_lit) -> LLit v) l)
	| LEList les     -> aux les
	| _              -> []


(* tr_list_cons *)
let encode_cons_equalities tr_ctx le_list les =
	let ctx = tr_ctx.z3_ctx in
	let aux les =
		if ((List.length les) = 0) then [] else
			let head = List.hd les in
			let tail = List.tl les in
			let head', _, _ = encode_logical_expression tr_ctx head in
			let tail', _, _ = encode_logical_expression tr_ctx (LEList tail) in
			let le_cons = (Expr.mk_app ctx tr_ctx.tr_list_cons [ head'; tail' ]) in
			[ Boolean.mk_eq ctx le_cons le_list ] in

	match les with
	| LLit (LList l) -> aux (List.map (fun v -> LLit v) l)
	| LEList les     -> aux les
	| _              -> []


let encode_snth_equalities tr_ctx s les =
	let ctx = tr_ctx.z3_ctx in
	List.mapi
		(fun i le ->
			let le', _, _ = encode_logical_expression tr_ctx le in
			let le_nth = (Expr.mk_app ctx tr_ctx.tr_snth_fun [ s; (mk_num_i ctx i) ]) in
			Boolean.mk_eq ctx le_nth le')
		les

let encode_gamma tr_ctx how_many =
	let ctx = tr_ctx.z3_ctx in
	let gamma = tr_ctx.tr_typing_env in
	let gamma_var_type_pairs = JSIL_Memory_Model.get_gamma_var_type_pairs gamma in
	let encoded_gamma = List.map
		(fun (x, t_x) ->
			if ((JSIL_Memory_Model.is_lvar_name x) || (JSIL_Memory_Model.is_abs_loc_name x))
				then (
				(match t_x with
				| NumberType
				| ListType   -> Boolean.mk_true ctx
				| _          ->
					let le_x = (mk_const ctx (Symbol.mk_string ctx x)) in
					let le_typeof_le_x = (Expr.mk_app ctx tr_ctx.tr_typeof_fun [ le_x ]) in
					let assertion = Boolean.mk_eq ctx le_typeof_le_x (encode_type ctx t_x) in
					assertion))
				else Boolean.mk_true ctx)
		gamma_var_type_pairs in
	if ((how_many = -1) || (List.length encoded_gamma <= how_many)) then encoded_gamma else
		(let rec get_n l n =
		 if (n = 0) then [] else
		 	(List.hd l) :: (get_n (List.tl l) (n-1)) in
		get_n encoded_gamma how_many)

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) ((String.make 1 s.[i]) :: l) in
  exp (String.length s - 1) []

(*
	We 'sort' logical expressions that are typable as lists as follows:
		1) List literals
		2) Logical lists
		3) Cons's
		4) Logical Variables
		5) Program Variables
*)
let sort_lists l1 l2 =
match l1, l2 with
| LLit (LList _), _ -> l1, l2
| _, LLit (LList _) -> l2, l1
| LEList _, _ -> l1, l2
| _, LEList _ -> l2, l1
| LBinOp (_, LstCons, _), _ -> l1, l2
| _, LBinOp (_, LstCons, _) -> l2, l1
| LVar _, _ -> l1, l2
| _, LVar _ -> l2, l1
| PVar _, PVar _ -> l1, l2
| _, _ ->
	raise(Failure (Printf.sprintf "Impossible: %s %s"
	               (JSIL_Print.string_of_logic_expression l1 false)
				   (JSIL_Print.string_of_logic_expression l2 false)))


let mk_simple_eq tr_ctx le1 le2 =
	let fe    = encode_logical_expression tr_ctx in
	let gamma = tr_ctx.tr_typing_env in
	let ctx   = tr_ctx.z3_ctx in
	let t1, _, _ = JSIL_Logic_Utils.type_lexpr gamma le1 in
	let t2, _, _ = JSIL_Logic_Utils.type_lexpr gamma le2 in
	let le1', t1', as1 = fe le1 in
	let le2', t2', as2 = fe le2 in
	match t1, t2 with
	| Some t1, Some t2 -> if (t1 <> t2) then [ Boolean.mk_false ctx ] else [ Boolean.mk_eq ctx le1' le2' ]
	| Some t1, None ->
		let t1' = encode_type ctx t1 in
		[ Boolean.mk_eq ctx le1' le2'; Boolean.mk_eq ctx t1' t2' ] @ as2
	| None, Some t2 ->
		let t2' = encode_type ctx t2 in
		[ Boolean.mk_eq ctx le1' le2'; Boolean.mk_eq ctx t1' t2' ] @ as1
	| None, None -> [ Boolean.mk_eq ctx le1' le2'; Boolean.mk_eq ctx t1' t2' ] @ as1 @ as2


let rec lets_do_some_list_theory_axioms tr_ctx l1 l2 =
	let f = lets_do_some_list_theory_axioms tr_ctx in
	let fe = encode_logical_expression tr_ctx in
	let l1, l2 = sort_lists l1 l2 in

	let ctx = tr_ctx.z3_ctx in
	(match l1, l2 with
 	(* Two literal lists, they have to be equal - ok *)
 	| LLit (LList l1), LLit (LList l2) ->
 		if (l1 = l2)
			then [ Boolean.mk_true ctx  ], []
			else [ Boolean.mk_false ctx ], []

	(* One literal list, one list of expressions - ok *)
 	| LLit (LList l1), LEList l2 ->
 		if (List.length l1 <> List.length l2) then [ Boolean.mk_false ctx ], [] else
		let l1 = List.map (fun x -> LLit x) l1 in
    List.fold_left2 (fun ac x y -> (mk_simple_eq tr_ctx x y) @ ac) [] l1 l2, []

	(* One literal list, one cons *)
 	| LLit (LList l1), LBinOp (e, LstCons, l2) ->
    if (List.length l1 = 0) then [ Boolean.mk_false ctx ], [] else
	 	let e' = LLit (List.hd l1) in
	 	let l1' = LLit (LList (List.tl l1)) in
		let assertions_head = mk_simple_eq tr_ctx e e' in
		let assertions_tail, axioms_tail = f l1' l2 in
		assertions_head @ assertions_tail, axioms_tail

 	(* One literal list, one variable *)
 	| LLit (LList l1'), LVar var
 	| LLit (LList l1'), PVar var ->
		let assertions  = mk_simple_eq tr_ctx l1 l2 in
		let l2', _, _   = fe l2 in
		let axiom_len   = Boolean.mk_eq ctx (Expr.mk_app ctx tr_ctx.tr_llen_fun [ l2' ]) (mk_num_i ctx (List.length l1')) in
	 	let axioms_nth  = encode_lnth_equalities tr_ctx l2' l1 in
		let axioms_cons = encode_cons_equalities tr_ctx l2' l1 in
		assertions, [ axiom_len ] @ axioms_cons @ axioms_nth

	(* Done with literal lists, now lists of logical expressions *)
 	(* Two lists of logical expressions *)
 	| LEList l1, LEList l2 ->
 		if (List.length l1 <> List.length l2) then [ Boolean.mk_false ctx ], [] else
    List.fold_left2 (fun ac x y -> (mk_simple_eq tr_ctx x y) @ ac) [] l1 l2, []

 	(* One logical list, one cons *)
	| LEList l1, LBinOp (e, LstCons, l2) ->
    if (List.length l1 = 0) then [ Boolean.mk_false ctx ], [] else
		let e' = List.hd l1 in
		let l1' = LEList (List.tl l1) in
	 	let assertions_head = mk_simple_eq tr_ctx e e' in
		let assertions_tail, axioms_tail = f l1' l2 in
		assertions_head @ assertions_tail, axioms_tail

	(* One logical list, one variable *)
 	| LEList le1, LVar var
 	| LEList le1, PVar var ->
		let assertions  = mk_simple_eq tr_ctx l1 l2 in
		let l2', _, _   = fe l2 in
		let axiom_len   = Boolean.mk_eq ctx (Expr.mk_app ctx tr_ctx.tr_llen_fun [ l2' ]) (mk_num_i ctx (List.length le1)) in
	 	let axioms_nth  = encode_lnth_equalities tr_ctx l2' l1 in
		let axioms_cons = encode_cons_equalities tr_ctx l2' l1 in
		assertions, [ axiom_len ] @ axioms_cons @ axioms_nth

 	(* Done with lists of logical expressions, here comes the cons *)
 	(* Two conses *)
 	| LBinOp (e1, LstCons, l1), LBinOp (e2, LstCons, l2) ->
  	let assertions_head = mk_simple_eq tr_ctx e1 e2 in
		let assertions_tail, axioms_tail = f l1 l2 in
		assertions_head @ assertions_tail, axioms_tail

	(* Cons and a variable *)
	| LBinOp (e1', LstCons, l1'), LVar var
 	| LBinOp (e1', LstCons, l1'), PVar var ->
 		(* Printf.printf "ConsVar: %s %s\n" (JSIL_Print.string_of_logic_expression l1 false) (JSIL_Print.string_of_logic_expression l2 false); *)
 	 	let assertions  = mk_simple_eq tr_ctx l1 l2 in
		let l2', _, _   = fe l2 in
		let axiom_len   =
			(match l1' with
			| LLit (LList l1'') -> Boolean.mk_eq ctx (Expr.mk_app ctx tr_ctx.tr_llen_fun [ l2' ]) (mk_num_i ctx (List.length l1''))
			| LEList l1''       -> Boolean.mk_eq ctx (Expr.mk_app ctx tr_ctx.tr_llen_fun [ l2' ]) (mk_num_i ctx (List.length l1''))
			| _                 ->
				let l1''', _, _ = fe l1' in
				let le_len_tail = (Expr.mk_app ctx tr_ctx.tr_llen_fun [ l1''' ]) in
				let le_len_tail_plus_one = Arithmetic.mk_add ctx [ (mk_num_i ctx 1); le_len_tail ] in
				Boolean.mk_eq ctx (Expr.mk_app ctx tr_ctx.tr_llen_fun [ l2' ]) le_len_tail_plus_one) in
		let axioms_nth  = encode_lnth_equalities tr_ctx l2' l1 in
		let axioms_cons = encode_cons_equalities tr_ctx l2' l1 in
		assertions, [ axiom_len ] @ axioms_cons @ axioms_nth

 | LVar _, LVar _
 | LVar _, PVar _
 | PVar _, PVar _ ->
	 let assertions = mk_simple_eq tr_ctx l1 l2 in
	 let l1', _, _   = fe l1 in
	 let l2', _, _   = fe l2 in
	 let axiom_len   = Boolean.mk_eq ctx (Expr.mk_app ctx tr_ctx.tr_llen_fun [ l1' ]) (Expr.mk_app ctx tr_ctx.tr_llen_fun [ l2' ]) in
	 let axioms_nth  = encode_lnth_equalities tr_ctx l1' l2 in
	 let axioms_cons = encode_cons_equalities tr_ctx l1' l2 in
	 assertions, [ axiom_len ] @ axioms_cons @ axioms_nth

 | _, _ -> Printf.printf "Oops! %s %s\n" (JSIL_Print.string_of_logic_expression l1 false) (JSIL_Print.string_of_logic_expression l2 false); exit 1
)


let make_concrete_string_axioms tr_ctx s =
	let ctx = tr_ctx.z3_ctx in
	let s', _, _  = encode_logical_expression tr_ctx (LLit (String s)) in
	let len_axiom = Boolean.mk_eq ctx (Expr.mk_app ctx tr_ctx.tr_slen_fun [ s' ]) (mk_num_i ctx (String.length s)) in
	let les = List.map (fun x -> LLit (String x)) (explode s) in
	let snth_axioms = encode_snth_equalities tr_ctx s' les in
	len_axiom :: snth_axioms


let rec lets_do_some_string_theory_axioms tr_ctx l1 l2 =
	let fe = encode_logical_expression tr_ctx in
	let ctx = tr_ctx.z3_ctx in

	(match l1, l2 with
	| LLit (String s1), LLit (String s2) -> if (s1 = s2) then [ Boolean.mk_true ctx ], [] else [ Boolean.mk_false ctx ], []

	| LStrNth (_, _), _
	| _, LStrNth (_, _) ->
		(* wrong encoding - there are axioms!!! *)
		(mk_simple_eq tr_ctx l1 l2), []

	| LLit (String s), _ ->
		let as1 = (mk_simple_eq tr_ctx l1 l2) in
		let l2', _, _ = fe l2 in
		let len_axiom = Boolean.mk_eq ctx (Expr.mk_app ctx tr_ctx.tr_slen_fun [ l2' ]) (mk_num_i ctx (String.length s)) in
		let les = List.map (fun x -> LLit (String x)) (explode s) in
		let snth_axioms = encode_snth_equalities tr_ctx l2' les in
		as1, len_axiom :: snth_axioms

	| _, LLit (String s) ->
		let as1 = (mk_simple_eq tr_ctx l1 l2) in
		let l1', _, _ = fe l1 in
		let len_axiom = Boolean.mk_eq ctx (Expr.mk_app ctx tr_ctx.tr_slen_fun [ l1' ]) (mk_num_i ctx (String.length s)) in
		let les = List.map (fun x -> LLit (String x)) (explode s) in
		let snth_axioms = encode_snth_equalities tr_ctx l1' les in
		as1, len_axiom :: snth_axioms

	| _, _ -> (mk_simple_eq tr_ctx l1 l2), [])



let if_some x f def = (match x with | Some y -> f y | None -> def)



let rec encode_assertion tr_ctx is_premise a : Expr.expr * (Expr.expr list) =
	let f = encode_assertion tr_ctx is_premise in
	let fe = encode_logical_expression tr_ctx in
	let ctx = tr_ctx.z3_ctx in
	let gamma = tr_ctx.tr_typing_env in

	(* Printf.printf ("EPF: %s, with gamma:\n%s\n") (JSIL_Print.string_of_logic_assertion a false) (JSIL_Memory_Print.string_of_gamma gamma); *)
	match a with
	| LNot a ->
		(* (Boolean.mk_and ctx (a' :: axioms)) *)
		let a', axioms = f a in
		Boolean.mk_not ctx a', []

	| LEq (le1, le2) ->
		let t1, _, _ = JSIL_Logic_Utils.type_lexpr gamma le1 in
		let t2, _, _ = JSIL_Logic_Utils.type_lexpr gamma le2 in

		(match t1, t2 with
		| Some ListType, Some ListType ->
			let encodings, axioms = lets_do_some_list_theory_axioms tr_ctx le1 le2 in
			(* let axioms = if is_premise then axioms else [] in  *)
			Boolean.mk_and ctx encodings, axioms

		| Some StringType, Some StringType ->
			let encodings, axioms = lets_do_some_string_theory_axioms tr_ctx le1 le2 in
			Boolean.mk_and ctx encodings, axioms

		| Some t1, Some t2 ->
			let le1', _, _ = fe le1 in
			let le2', _, _ = fe le2 in
			if (t1 = t2)
				then Boolean.mk_eq ctx le2' le1', []
				else Boolean.mk_false ctx, []

		| _, _ ->
			let le1', t1', as1 = fe le1 in
			let le2', t2', as2 = fe le2 in
			let cur_as1 = Boolean.mk_eq ctx le1' le2' in
			let cur_as2 = Boolean.mk_eq ctx t1' t2' in
			Boolean.mk_and ctx ([ cur_as1; cur_as2 ] @ as1 @ as2), [])

	| LLess (le1, le2) ->
		let t1, _, _ = JSIL_Logic_Utils.type_lexpr gamma le1 in
		let t2, _, _ = JSIL_Logic_Utils.type_lexpr gamma le2 in

		let le1', t1', as1 = fe le1 in
		let le2', t2', as2 = fe le2 in
		(match t1, t2 with
		| Some t1, Some t2 ->
			let t = types_lub t1 t2 in
			(match t with
			| Some IntType
			| Some NumberType -> Arithmetic.mk_lt ctx le1' le2', []
			| _ -> Printf.printf "Coucou!! T'habites dans quelle planete?\n"; raise (Failure "Arithmetic operation invoked on non-numeric types"))

    | _, _ ->
			(* TO DO - we need to encode the appropriate type constraints *)
			(Printf.printf "LLess Error: %s %s. gamma: %s\n"
				(JSIL_Print.string_of_logic_expression le1 false)
				(JSIL_Print.string_of_logic_expression le2 false)
				(JSIL_Memory_Print.string_of_gamma gamma);
			raise (Failure "Death.")))


	| LLessEq (le1, le2) ->
		let t1, _, _ = JSIL_Logic_Utils.type_lexpr gamma le1 in
		let t2, _, _ = JSIL_Logic_Utils.type_lexpr gamma le2 in

		let le1', t1', as1 = fe le1 in
		let le2', t2', as2 = fe le2 in

		(match t1, t2 with
		| Some t1, Some t2 ->
			let t = types_lub t1 t2 in
			(match t with
			| Some IntType
			| Some NumberType -> Arithmetic.mk_le ctx le1' le2', []
			| _ -> Printf.printf "Coucou!! T'habites dans quelle planete?\n";
				   raise (Failure "Arithmetic operation invoked on non-numeric types"))

    | _, _ ->
			(* TO DO - we need to encode the appropriate type constraints *)
			(Printf.printf "LLess Error: %s %s. gamma: %s\n"
				(JSIL_Print.string_of_logic_expression le1 false)
				(JSIL_Print.string_of_logic_expression le2 false)
				(JSIL_Memory_Print.string_of_gamma gamma);
			raise (Failure "Death.")))

	| LStrLess (_, _)    ->
		(* TO DO - uninterpreted function *)
		raise (Failure ("I don't know how to do string comparison in Z3"))

	| LTrue	-> Boolean.mk_true ctx, []

	| LFalse -> Boolean.mk_false ctx, []

	| LOr (a1, a2) ->
		let a1', axioms1 = f a1 in
		let a2', axioms2 = f a2 in
		let a1'' = Boolean.mk_and ctx (a1' :: axioms1) in
		let a2'' = Boolean.mk_and ctx (a2' :: axioms2) in
		Boolean.mk_or ctx [ a1''; a2'' ], []

	| LAnd (a1, a2) ->
		let a1', axioms1 = f a1 in
		let a2', axioms2 = f a2 in
		Boolean.mk_and ctx ([ a1'; a2' ] @ axioms1 @ axioms2), []

	| _                  ->
		let msg = Printf.sprintf "Unsupported assertion to encode for Z3: %s" (JSIL_Print.string_of_logic_assertion a false) in
		raise (Failure msg)


let encode_assertion_top_level tr_ctx is_premise a =
	let a_strings = JSIL_Logic_Utils.remove_string_duplicates (JSIL_Logic_Utils.get_assertion_string_literals a) in
	let a' = JSIL_Logic_Utils.push_in_negations_off a in
	let a'', axioms = encode_assertion tr_ctx is_premise a in
	let a_strings_axioms = List.concat (List.map (fun s -> make_concrete_string_axioms tr_ctx s) a_strings) in
	if (((List.length axioms) > 0) || ((List.length a_strings_axioms) > 0))
		then Boolean.mk_and tr_ctx.z3_ctx (a'' :: (axioms @ a_strings_axioms))
		else a''


let extend_solver solver pfs gamma = ()


let string_of_z3_expr_list exprs =
	List.fold_left
		(fun ac e ->
			let e_str = Expr.to_string e in
			if (ac = "") then e_str else (ac ^ ",\n" ^ e_str))
		""
		exprs

let get_new_solver assertions gamma existentials =
	let tr_ctx = mk_smt_translation_ctx gamma existentials in
	let assertions = List.map (fun a -> encode_assertion_top_level tr_ctx true a) assertions in
	let assertions = tr_ctx.tr_axioms @ (encode_gamma tr_ctx (-1)) @ assertions in
	let solver = (Solver.mk_solver tr_ctx.z3_ctx None) in
	Solver.add solver assertions;
	(* Printf.printf "I have just created a solver with the content given by:\n: %s\n" (string_of_z3_expr_list assertions); *)
	solver


let dispose_solver solver =
	Gc.full_major ();
	Solver.reset solver


let print_model solver =
	let model = Solver.get_model solver in
	match model with
	| Some model ->
		let str_model = Model.to_string model in
		Printf.printf "I found the model: \n\n%s\n\n" str_model
	| None ->
		Printf.printf "No model filha\n"

let string_of_solver solver =
	let exprs = Solver.get_assertions solver in
	string_of_z3_expr_list exprs

let check_satisfiability assertions gamma existentials =
	let solver = get_new_solver assertions gamma existentials in
	(* Printf.printf "CS Solver: \n%s\n" (string_of_solver solver); *)
	let ret = (Solver.check solver []) = Solver.SATISFIABLE in
	(* Printf.printf "Satisfiability check of right side: %b\n" ret; *)
	ret

(* right_as must be satisfiable *)
let rec old_check_entailment existentials left_as right_as gamma =

	let tr_ctx = mk_smt_translation_ctx gamma existentials in
	let ctx = tr_ctx.z3_ctx in

	let check_entailment_aux () =
		Gc.full_major ();
		let old_left_as = left_as in
		let left_as = List.map (fun a -> encode_assertion_top_level tr_ctx true a) left_as in
		let left_as = tr_ctx.tr_axioms @ (encode_gamma tr_ctx (-1)) @ left_as in
		let right_as = List.map (fun a -> encode_assertion_top_level tr_ctx false (LNot a)) right_as in
		let right_as_or =
			if ((List.length right_as) > 1) then
				(Boolean.mk_or ctx right_as)
			else if ((List.length right_as) = 1) then
				(List.nth right_as 0)
			else Boolean.mk_false ctx in

		let right_as_or =
			if ((List.length existentials) > 0)
				then encode_quantifier true tr_ctx.z3_ctx existentials (get_sorts tr_ctx existentials) right_as_or
				else right_as_or in
		let right_as_or = Expr.simplify right_as_or None in

		(* Printf.printf "Checking if the current state entails the NEGATION of the following:\n%s\n" (Expr.to_string right_as_or); *)

		let solver = (Solver.mk_solver tr_ctx.z3_ctx None) in
		Solver.add solver left_as;

		let ret_left_side = (Solver.check solver [ ]) = Solver.SATISFIABLE in
		(* Printf.printf "I am checking the satisfiability of the left side and got: %b\n" ret_left_side; *)

		Solver.push solver;
		Solver.add solver [ right_as_or ];

		(* Printf.printf "I am checking the satisfiability of:\n %s\n" (string_of_solver solver); *)
		let ret = (Solver.check solver [ ]) != Solver.SATISFIABLE in

		(* if (not ret) then print_model solver; *)

		(*  Printf.printf "backtracking_scopes before pop after push: %d!!!\n" (Solver.get_num_scopes solver);
		Printf.printf "ret: %b\n" ret; *)
		Solver.pop solver 1;
		ret, Some (solver, tr_ctx)  in

	(* if (not (ret_right)) then false, None *)
	try check_entailment_aux () with Failure msg -> Printf.printf "Horrible failure\n"; false, None



let rec check_entailment solver existentials left_as right_as gamma =
	(* Printf.printf "Entering check entailment...\n"; *)

	if ((List.length right_as) = 0) then true
	else if (not (check_satisfiability right_as gamma existentials)) then false
	else (
	match !solver with
	| Some (solver, tr_ctx) ->
		(* Printf.printf "check_entailment and there is already a solver. backtracking_scopes: %d!!!\n" (Solver.get_num_scopes solver); *)
		let ctx = tr_ctx.z3_ctx in
		let tr_ctx = { tr_ctx with tr_typing_env = gamma } in
		let not_right_as = List.map (fun a -> encode_assertion_top_level tr_ctx false (LNot a)) right_as in
		let len_not_right_as = List.length not_right_as in
		let right_as_or =
			if (len_not_right_as > 1) then
				(Boolean.mk_or ctx not_right_as)
			else if (len_not_right_as = 1) then
				(List.nth not_right_as 0)
			else Boolean.mk_false ctx in
		let right_as_or =
			if ((List.length existentials) > 0)
				then encode_quantifier true ctx existentials (get_sorts tr_ctx existentials) right_as_or
				else right_as_or in
		let right_as_or = Expr.simplify right_as_or None in

		Solver.push solver;
		Solver.add solver [ right_as_or ];
		(* Printf.printf "I am checking the satisfiability of:\n %s\n" (string_of_solver solver); *)
		let ret = (Solver.check solver [ ]) != Solver.SATISFIABLE in
		(* Printf.printf "backtracking_scopes before pop after push: %d!!!\n" (Solver.get_num_scopes solver);
		Printf.printf "ret: %b\n" ret; *)
		Solver.pop solver 1;
		(* Printf.printf "backtracking_scopes after pop: %d!!!\n" (Solver.get_num_scopes solver); *)
		ret

	| None ->
		(* Printf.printf "check_entailment with NO solver!!!\n"; *)
		let ret, new_solver = old_check_entailment existentials left_as right_as gamma in
		(match new_solver with
		| Some (new_solver, tr_ctx) -> solver := Some (new_solver, tr_ctx)
		| None                      -> ());
		ret)




let is_equal e1 e2 pure_formulae solver gamma =
    (* Printf.printf "Checking if %s is equal to %s given that: %s\n;" (JSIL_Print.string_of_logic_expression e1 false) (JSIL_Print.string_of_logic_expression e2 false) (JSIL_Memory_Print.string_of_shallow_p_formulae pure_formulae false);
    Printf.printf "and the gamma is: %s\n" (JSIL_Memory_Print.string_of_gamma gamma); *)
	match e1, e2 with
	| LLit l1, LLit l2 -> l1 = l2
	| ALoc aloc1 , ALoc aloc2 -> aloc1 = aloc2
	| LNone, LNone -> true
	| LUnknown, LUnknown -> false
	| LVar l1, LVar l2 ->
		if (l1 = l2)
			then true
			else check_entailment solver [] (JSIL_Memory_Model.pfs_to_list pure_formulae) [ (LEq (e1, e2)) ] gamma
	| _, _ -> check_entailment solver [] (JSIL_Memory_Model.pfs_to_list pure_formulae) [ (LEq (e1, e2)) ] gamma


let is_different e1 e2 pure_formulae solver gamma =
	match e1, e2 with
	| LLit l1, LLit l2 -> (not (l1 = l2))
	| ALoc aloc1, ALoc aloc2 -> (not (aloc1 = aloc2))
	| _, _ -> check_entailment solver [] (JSIL_Memory_Model.pfs_to_list pure_formulae) [ (LNot (LEq (e1, e2))) ] gamma
