open JSIL_Syntax
open Symbolic_State
open JSIL_Logic_Utils
open Z3
open Z3.Set

let _ = print_debug_petar "Entering pure entailment."

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
	llen_fun            : FuncDecl.func_decl;
	slen_fun            : FuncDecl.func_decl;
	num2str_fun         : FuncDecl.func_decl;
	str2num_fun         : FuncDecl.func_decl;
	num2int_fun         : FuncDecl.func_decl;
	lnth_fun            : FuncDecl.func_decl;
	snth_fun            : FuncDecl.func_decl;
	lcat_fun            : FuncDecl.func_decl
}

type jsil_type_constructors = {
	undefined_type_constructor : FuncDecl.func_decl;
	null_type_constructor      : FuncDecl.func_decl;
	empty_type_constructor     : FuncDecl.func_decl;
	none_type_constructor      : FuncDecl.func_decl;
	boolean_type_constructor   : FuncDecl.func_decl;
	number_type_constructor    : FuncDecl.func_decl;
	char_type_constructor      : FuncDecl.func_decl;
	string_type_constructor    : FuncDecl.func_decl;
	object_type_constructor    : FuncDecl.func_decl;
  list_type_constructor      : FuncDecl.func_decl;
	type_type_constructor      : FuncDecl.func_decl;
	set_type_constructor       : FuncDecl.func_decl
}

type z3_basic_jsil_value = {
  (****************)
  (* constructors *)
  (****************)
  undefined_constructor : FuncDecl.func_decl;
  null_constructor      : FuncDecl.func_decl;
  empty_constructor     : FuncDecl.func_decl;
  boolean_constructor   : FuncDecl.func_decl;
  number_constructor    : FuncDecl.func_decl;
  char_constructor      : FuncDecl.func_decl;
  string_constructor    : FuncDecl.func_decl;
  loc_constructor       : FuncDecl.func_decl;
  type_constructor      : FuncDecl.func_decl;
  list_constructor      : FuncDecl.func_decl;
  none_constructor      : FuncDecl.func_decl;
  (*************)
  (* accessors *)
  (*************)
  boolean_accessor      : FuncDecl.func_decl;
  number_accessor       : FuncDecl.func_decl;
  char_accessor         : FuncDecl.func_decl;
  string_accessor       : FuncDecl.func_decl;
  loc_accessor          : FuncDecl.func_decl;
  type_accessor         : FuncDecl.func_decl;
  list_accessor         : FuncDecl.func_decl;
  (***************)
  (* recognizers *)
  (***************) 
  undefined_recognizer  : FuncDecl.func_decl;
  null_recognizer       : FuncDecl.func_decl;
  empty_recognizer      : FuncDecl.func_decl;
  boolean_recognizer    : FuncDecl.func_decl;
  number_recognizer     : FuncDecl.func_decl;
  char_recognizer       : FuncDecl.func_decl;
  string_recognizer     : FuncDecl.func_decl;
  loc_recognizer        : FuncDecl.func_decl;
  type_recognizer       : FuncDecl.func_decl;
  list_recognizer       : FuncDecl.func_decl;
  none_recognizer       : FuncDecl.func_decl
}

type z3_jsil_list = {
	(** constructors **)
	nil_constructor       : FuncDecl.func_decl;
	cons_constructor      : FuncDecl.func_decl;
	(** accessors    **)
	head_accessor         : FuncDecl.func_decl;
	tail_accessor         : FuncDecl.func_decl;
	(** recognizers **)
	nil_recognizer        : FuncDecl.func_decl;
	cons_recognizer       : FuncDecl.func_decl
}

type extended_jsil_value_constructor = {
	singular_constructor       : FuncDecl.func_decl;
	set_constructor            : FuncDecl.func_decl;
	singular_elem_accessor     : FuncDecl.func_decl;
	set_accessor               : FuncDecl.func_decl;
	singular_elem_recognizer   : FuncDecl.func_decl;
	set_recognizer             : FuncDecl.func_decl
}

let _ = print_debug_petar "Extended JSIL ."

let cfg = [("model", "true"); ("proof", "true"); ("unsat_core", "true")]
let ctx : Z3.context = (mk_context cfg)

let _ = print_debug_petar "Context defined."

let booleans_sort = Boolean.mk_sort ctx
let ints_sort     = Arithmetic.Integer.mk_sort ctx
let reals_sort    = Arithmetic.Real.mk_sort ctx
let fp_sort       = FloatingPoint.mk_sort_64 ctx
let numbers_sort  = match_enc "mk_sort" reals_sort fp_sort

let _ = print_debug_petar "Sorts defined."

let rm = FloatingPoint.mk_const ctx (Symbol.mk_string ctx "rm") (FloatingPoint.RoundingMode.mk_sort ctx)
let mk_string_symb s = Symbol.mk_string ctx s

let mk_int_i      = Arithmetic.Integer.mk_numeral_i ctx
let mk_const_i    = Arithmetic.Integer.mk_const ctx

let mk_const      = match_enc "mk_const" (Arithmetic.Real.mk_const ctx)     (fun (s : Symbol.symbol) -> FloatingPoint.mk_const ctx s fp_sort)
let mk_num_i      = match_enc "mk_num_i" (Arithmetic.Real.mk_numeral_i ctx) (fun i -> FloatingPoint.mk_numeral_i ctx i fp_sort)
let mk_num_s      = match_enc "mk_num_s" (Arithmetic.Real.mk_numeral_s ctx) (fun s -> FloatingPoint.mk_numeral_s ctx s fp_sort)
let mk_lt         = match_enc "mk_lt"    Arithmetic.mk_lt                   FloatingPoint.mk_lt
let mk_le         = match_enc "mk_le"    Arithmetic.mk_le                   FloatingPoint.mk_leq
let mk_ge         = match_enc "mk_ge"    Arithmetic.mk_ge                   FloatingPoint.mk_geq

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
				"NumberType"; "CharType"; "StringType"; "ObjectType"; "ListType"; "TypeType"; "SetType"
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
		let char_type_constructor      = List.nth z3_jsil_type_constructors 6 in
		let string_type_constructor    = List.nth z3_jsil_type_constructors 7 in
		let object_type_constructor    = List.nth z3_jsil_type_constructors 8 in
		let list_type_constructor      = List.nth z3_jsil_type_constructors 9 in
		let type_type_constructor      = List.nth z3_jsil_type_constructors 10 in
		let set_type_constructor       = List.nth z3_jsil_type_constructors 11 in
		{
			undefined_type_constructor = undefined_type_constructor;
			null_type_constructor      = null_type_constructor;
			empty_type_constructor     = empty_type_constructor;
			none_type_constructor      = none_type_constructor;
			boolean_type_constructor   = boolean_type_constructor;
			number_type_constructor    = number_type_constructor;
			char_type_constructor      = char_type_constructor;
			string_type_constructor    = string_type_constructor;
			object_type_constructor    = object_type_constructor;
			list_type_constructor      = list_type_constructor;
			type_type_constructor      = type_type_constructor;
			set_type_constructor       = set_type_constructor
		}

	with _ -> raise (Failure ("DEATH: type_operations"))


let z3_jsil_literal_sort, z3_jsil_list_sort, lit_operations, list_operations =
	(* JSIL type constructors *)
	let jsil_undefined_constructor =
		Datatype.mk_constructor ctx (mk_string_symb "Undefined") (mk_string_symb "isUndefined") [] [] [] in
	let jsil_null_constructor =
		Datatype.mk_constructor ctx (mk_string_symb "Null") (mk_string_symb "isNull") [] [] [] in
	let jsil_empty_constructor =
		Datatype.mk_constructor ctx (mk_string_symb "Empty") (mk_string_symb "isEmpty") [] [] [] in
	let jsil_bool_constructor =
		Datatype.mk_constructor ctx (mk_string_symb "Bool") (mk_string_symb "isBool")
			[ (mk_string_symb "bValue") ] [ Some booleans_sort ] [ 0 ] in
	let jsil_num_constructor =
		Datatype.mk_constructor ctx (mk_string_symb "Num") (mk_string_symb "isNum")
			[ (mk_string_symb "nValue") ] [ Some numbers_sort ] [ 0 ] in
	let jsil_char_constructor =
		Datatype.mk_constructor ctx (mk_string_symb "Char") (mk_string_symb "isChar")
			[ (mk_string_symb "cValue") ] [ Some ints_sort ] [ 0 ] in
	let jsil_string_constructor =
		Datatype.mk_constructor ctx (mk_string_symb "String") (mk_string_symb "isString")
			[ (mk_string_symb "sValue") ] [ Some ints_sort ] [ 0 ] in
	let jsil_loc_constructor =
		Datatype.mk_constructor ctx (mk_string_symb "Loc") (mk_string_symb "isLoc")
			[ (mk_string_symb "locValue") ] [ Some ints_sort ] [ 0 ] in
	let jsil_type_constructor =
		Datatype.mk_constructor ctx (mk_string_symb "Type") (mk_string_symb "isType")
			[ (mk_string_symb "tValue") ] [ Some z3_jsil_type_sort ] [ 0 ] in
	let jsil_list_constructor =
		Datatype.mk_constructor ctx (mk_string_symb "List") (mk_string_symb "isList")
			[ (mk_string_symb "listValue") ] [ None ] [ 1 ] in
	let jsil_none_constructor =
		Datatype.mk_constructor ctx (mk_string_symb "None") (mk_string_symb "isNone") [] [] [] in

	(* JSIL List Type constructors *)
	let jsil_list_nil_constructor =
		Datatype.mk_constructor ctx (mk_string_symb "Nil") (mk_string_symb "isNil") [] [] [] in
	let jsil_list_cons_constructor =
		Datatype.mk_constructor ctx (mk_string_symb "Cons") (mk_string_symb "isCons")
			[ (mk_string_symb "head"); (mk_string_symb "tail") ] [ None; None ] [ 0; 1 ] in

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
					jsil_char_constructor;
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

		let jsil_list_constructors    = Datatype.get_constructors z3_jsil_list_sort in
		let nil_constructor           = List.nth jsil_list_constructors 0 in
		let cons_constructor          = List.nth jsil_list_constructors 1 in

		let jsil_list_accessors       = Datatype.get_accessors z3_jsil_list_sort in
		let head_accessor             = List.nth (List.nth jsil_list_accessors 1) 0 in
		let tail_accessor             = List.nth (List.nth jsil_list_accessors 1) 1 in

		let jsil_list_recognizers     = Datatype.get_recognizers z3_jsil_list_sort in
		let nil_recognizer            = List.nth jsil_list_recognizers 0 in
		let cons_recognizer           = List.nth jsil_list_recognizers 1 in

		let z3_literal_constructors   = Datatype.get_constructors z3_jsil_literal_sort in
		let undefined_constructor     = List.nth z3_literal_constructors 0 in
		let null_constructor          = List.nth z3_literal_constructors 1 in
		let empty_constructor         = List.nth z3_literal_constructors 2 in
		let boolean_constructor       = List.nth z3_literal_constructors 3 in
		let number_constructor        = List.nth z3_literal_constructors 4 in
		let char_constructor          = List.nth z3_literal_constructors 5 in
		let string_constructor        = List.nth z3_literal_constructors 6 in
		let loc_constructor           = List.nth z3_literal_constructors 7 in
		let type_constructor          = List.nth z3_literal_constructors 8 in
		let list_constructor          = List.nth z3_literal_constructors 9 in
		let none_constructor          = List.nth z3_literal_constructors 10 in

		let jsil_literal_accessors    = Datatype.get_accessors z3_jsil_literal_sort in
		let boolean_accessor          = List.nth (List.nth jsil_literal_accessors 3) 0 in
		let number_accessor           = List.nth (List.nth jsil_literal_accessors 4) 0 in
		let char_accessor             = List.nth (List.nth jsil_literal_accessors 5) 0 in
		let string_accessor           = List.nth (List.nth jsil_literal_accessors 6) 0 in
		let loc_accessor              = List.nth (List.nth jsil_literal_accessors 7) 0 in
		let type_accessor             = List.nth (List.nth jsil_literal_accessors 8) 0 in
		let list_accessor             = List.nth (List.nth jsil_literal_accessors 9) 0 in

		let jsil_literal_recognizers  = Datatype.get_recognizers z3_jsil_literal_sort in
		let undefined_recognizer      = List.nth jsil_literal_recognizers 0 in
		let null_recognizer           = List.nth jsil_literal_recognizers 1 in
		let empty_recognizer          = List.nth jsil_literal_recognizers 2 in
		let boolean_recognizer        = List.nth jsil_literal_recognizers 3 in
		let number_recognizer         = List.nth jsil_literal_recognizers 4 in
		let char_recognizer           = List.nth jsil_literal_recognizers 5 in
		let string_recognizer         = List.nth jsil_literal_recognizers 6 in
		let loc_recognizer            = List.nth jsil_literal_recognizers 7 in
		let type_recognizer           = List.nth jsil_literal_recognizers 8 in
		let list_recognizer           = List.nth jsil_literal_recognizers 9 in
		let none_recognizer           = List.nth jsil_literal_recognizers 10 in

		let jsil_literal_operations   = {
			(** constructors **)
			undefined_constructor = undefined_constructor;
			null_constructor      = null_constructor;
			empty_constructor     = empty_constructor;
			boolean_constructor   = boolean_constructor;
			number_constructor    = number_constructor;
			char_constructor      = char_constructor;
			string_constructor    = string_constructor;
			loc_constructor       = loc_constructor;
			type_constructor      = type_constructor;
			list_constructor      = list_constructor;
			none_constructor      = none_constructor;
			(** accessors **)
			boolean_accessor      = boolean_accessor;
			number_accessor       = number_accessor;
			char_accessor         = char_accessor;
			string_accessor       = string_accessor;
			loc_accessor          = loc_accessor;
			type_accessor         = type_accessor;
			list_accessor         = list_accessor;
			(** recognizers **)
			undefined_recognizer  = undefined_recognizer;
			null_recognizer       = null_recognizer;
			empty_recognizer      = empty_recognizer;
			boolean_recognizer    = boolean_recognizer;
			number_recognizer     = number_recognizer;
			char_recognizer       = char_recognizer;
			string_recognizer     = string_recognizer;
			loc_recognizer        = loc_recognizer;
			type_recognizer       = type_recognizer;
			list_recognizer       = list_recognizer;
			none_recognizer       = none_recognizer
		}  in
		let jsil_list_operations = {
			(** constructors **)
			nil_constructor       = nil_constructor;
			cons_constructor      = cons_constructor;
			(** accessors **)
			head_accessor         = head_accessor;
			tail_accessor         = tail_accessor;
			(** recognizers **)
			nil_recognizer        = nil_recognizer;
			cons_recognizer       = cons_recognizer
		} in
		z3_jsil_literal_sort, z3_jsil_list_sort, jsil_literal_operations, jsil_list_operations
	with _ -> raise (Failure ("DEATH: construction of z3_jsil_value_sort"))


let extended_literal_sort, extended_literal_operations, z3_jsil_set_sort =
	let z3_jsil_set_sort = Set.mk_sort ctx z3_jsil_literal_sort in

	let jsil_sing_elem_constructor =
		Datatype.mk_constructor ctx (mk_string_symb "Elem") (mk_string_symb "isSingular")
			[ (mk_string_symb "singElem") ]  [ Some z3_jsil_literal_sort ] [ 0 ] in

	let jsil_set_elem_constructor =
		Datatype.mk_constructor ctx (mk_string_symb "Set") (mk_string_symb "isSet")
			[ (mk_string_symb "setElem") ]  [ Some z3_jsil_set_sort ] [ 0 ] in

	let extended_literal_sort =
		Datatype.mk_sort ctx (mk_string_symb "Extended_JSIL_Literal")
			[ jsil_sing_elem_constructor; jsil_set_elem_constructor ] in

	try
		let jsil_extended_literal_constructors = Datatype.get_constructors extended_literal_sort in
		let singular_constructor               = List.nth jsil_extended_literal_constructors 0 in
		let set_constructor                    = List.nth jsil_extended_literal_constructors 1 in

		let jsil_extended_literal_accessors    = Datatype.get_accessors extended_literal_sort in
		let singular_elem_accessor             = List.nth (List.nth jsil_extended_literal_accessors 0) 0 in
		let set_accessor                       = List.nth (List.nth jsil_extended_literal_accessors 1) 0 in

		let jsil_extended_literal_recognizers  = Datatype.get_recognizers extended_literal_sort in
		let singular_elem_recognizer           = List.nth jsil_extended_literal_recognizers 0 in
		let set_recognizer                     = List.nth jsil_extended_literal_recognizers 1 in

		let extended_literal_operations   = {
			singular_constructor       = singular_constructor;
			set_constructor            = set_constructor;
			singular_elem_accessor     = singular_elem_accessor;
			set_accessor               = set_accessor;
			singular_elem_recognizer   = singular_elem_recognizer;
			set_recognizer             = set_recognizer
		} in
		extended_literal_sort, extended_literal_operations, z3_jsil_set_sort
	with _ -> raise (Failure ("DEATH: construction of z3_jsil_value_sort"))


let mk_singleton_elem ele = Expr.mk_app ctx extended_literal_operations.singular_constructor [ ele ]
let mk_singleton_access ele =  Expr.mk_app ctx extended_literal_operations.singular_elem_accessor [ ele ]

let axiomatised_operations =

	let slen_fun        = FuncDecl.mk_func_decl ctx (mk_string_symb "s-len")
							[ ints_sort ] numbers_sort in
	let llen_fun        = FuncDecl.mk_func_decl ctx (mk_string_symb "l-len")
							[ z3_jsil_list_sort ] numbers_sort in
	let num2str_fun     = FuncDecl.mk_func_decl ctx (mk_string_symb "num2str")
							[ numbers_sort ] numbers_sort in
	let str2num_fun     = FuncDecl.mk_func_decl ctx (mk_string_symb "str2num")
							[ numbers_sort ] numbers_sort in
	let num2int_fun     = FuncDecl.mk_func_decl ctx (mk_string_symb "num2int")
							[ numbers_sort ] numbers_sort in
	let snth_fun        = FuncDecl.mk_func_decl ctx (mk_string_symb "s-nth")
							[ ints_sort; ints_sort ] ints_sort in
	let lnth_fun        = FuncDecl.mk_func_decl ctx (mk_string_symb "l-nth")
							[ z3_jsil_list_sort; ints_sort ] z3_jsil_literal_sort in
	let lcat_fun        = FuncDecl.mk_func_decl ctx (mk_string_symb "l-cat")
							[ z3_jsil_list_sort; z3_jsil_list_sort ] z3_jsil_list_sort in

	{
		slen_fun     = slen_fun;
		llen_fun     = llen_fun;
		num2str_fun  = num2str_fun;
		str2num_fun  = str2num_fun;
		num2int_fun  = num2int_fun;
		snth_fun     = snth_fun;
		lnth_fun     = lnth_fun;
		lcat_fun     = lcat_fun
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

let mk_z3_set les =
	let empty_set = Set.mk_empty ctx z3_jsil_literal_sort in
	let rec loop les cur_set =
		match les with
		| [] -> cur_set
		| le :: rest_les ->
			let new_cur_set = Set.mk_set_add ctx cur_set le in
			loop rest_les new_cur_set in
	let result = loop les empty_set in
	result

let mk_z3_list les nil_constructor cons_constructor =
	try
		mk_z3_list_core (List.rev les) nil_constructor cons_constructor
	with _ -> raise (Failure "DEATH: mk_z3_list")

let str_codes = Hashtbl.create 1000
let str_counter = ref 0
let encode_string str =
	try
		let str_number : int = Hashtbl.find str_codes str in
		let z3_code = mk_int_i str_number in
		z3_code
	with Not_found ->
		let z3_code = mk_int_i !str_counter in
		Hashtbl.add str_codes str (!str_counter);
		str_counter := !str_counter + 1;
		z3_code

let encode_type t =
	try
		match t with
		| UndefinedType -> Expr.mk_app ctx type_operations.undefined_type_constructor []
		| NullType      -> Expr.mk_app ctx type_operations.null_type_constructor      []
		| EmptyType     -> Expr.mk_app ctx type_operations.empty_type_constructor     []
		| NoneType      -> Expr.mk_app ctx type_operations.none_type_constructor      []
		| BooleanType   -> Expr.mk_app ctx type_operations.boolean_type_constructor   []
		| NumberType    -> Expr.mk_app ctx type_operations.number_type_constructor    []
		| CharType	    -> Expr.mk_app ctx type_operations.char_type_constructor      []
		| StringType    -> Expr.mk_app ctx type_operations.string_type_constructor    []
		| ObjectType    -> Expr.mk_app ctx type_operations.object_type_constructor    []
		| ListType      -> Expr.mk_app ctx type_operations.list_type_constructor      []
		| TypeType      -> Expr.mk_app ctx type_operations.type_type_constructor      []
		| SetType       -> Expr.mk_app ctx type_operations.set_type_constructor       []
	with _ ->
		raise (Failure (Printf.sprintf "DEATH: encode_type with arg: %s" (JSIL_Print.string_of_type t)))


let typeof_expression x =
	let set_guard       = Expr.mk_app ctx extended_literal_operations.set_recognizer [ x ] in
	let sing_elem_guard = Expr.mk_app ctx extended_literal_operations.singular_elem_recognizer [ x ] in

	let elem_x = mk_singleton_access x in
	let undefined_guard = Expr.mk_app ctx lit_operations.undefined_recognizer [ elem_x ] in
	let null_guard      = Expr.mk_app ctx lit_operations.null_recognizer      [ elem_x ] in
	let empty_guard     = Expr.mk_app ctx lit_operations.empty_recognizer     [ elem_x ] in
	let boolean_guard   = Expr.mk_app ctx lit_operations.boolean_recognizer   [ elem_x ] in
	let number_guard    = Expr.mk_app ctx lit_operations.number_recognizer    [ elem_x ] in
	let char_guard      = Expr.mk_app ctx lit_operations.char_recognizer      [ elem_x ] in
	let string_guard    = Expr.mk_app ctx lit_operations.string_recognizer    [ elem_x ] in
	let loc_guard       = Expr.mk_app ctx lit_operations.loc_recognizer       [ elem_x ] in
	let type_guard      = Expr.mk_app ctx lit_operations.type_recognizer      [ elem_x ] in
	let list_guard      = Expr.mk_app ctx lit_operations.list_recognizer      [ elem_x ] in
	let none_guard      = Expr.mk_app ctx lit_operations.none_recognizer      [ elem_x ] in

	let sing_elem_types_guards = [
		undefined_guard; null_guard; empty_guard; boolean_guard;
		number_guard; char_guard; string_guard; loc_guard;
		type_guard; list_guard; none_guard
	] in

	let sing_elem_types_guards =
		List.map (fun a -> Boolean.mk_and ctx [sing_elem_guard; a]) sing_elem_types_guards in

  	let guards = set_guard :: sing_elem_types_guards in
  	let results =
  		List.map encode_type
  			[ SetType; UndefinedType; NullType; EmptyType; BooleanType;
 				NumberType; CharType; StringType; ObjectType; TypeType; ListType; NoneType ] in

 	let rec loop guards results =
 		match guards, results with
 		| [], _
 		| _, [] -> raise (Failure "DEATH: typeof_expression")
 		| [ _ ], res :: _ -> res
 		| guard :: rest_guards, res :: rest_results ->
 			Boolean.mk_ite ctx guard res (loop rest_guards rest_results) in

 	loop guards results


let rec encode_lit lit =

	let mk_singleton_elem ele = Expr.mk_app ctx extended_literal_operations.singular_constructor [ ele ] in

	try
		match lit with
		| Undefined -> mk_singleton_elem (Expr.mk_app ctx lit_operations.undefined_constructor [])
		| Null      -> mk_singleton_elem (Expr.mk_app ctx lit_operations.null_constructor      [])
		| Empty     -> mk_singleton_elem (Expr.mk_app ctx lit_operations.empty_constructor     [])

		| Bool b ->
			let b_arg =
				match b with
				| true  -> Boolean.mk_true ctx
				| false -> Boolean.mk_false ctx in
			mk_singleton_elem (Expr.mk_app ctx lit_operations.boolean_constructor [ b_arg ])

		| Num n ->
			let sfn = string_of_float n in
			let n_arg = mk_num_s sfn in
			mk_singleton_elem (Expr.mk_app ctx lit_operations.number_constructor [ n_arg ])

		| Char c ->
			let s_arg = encode_string (String.make 1 c) in
			mk_singleton_elem (Expr.mk_app ctx lit_operations.char_constructor [ s_arg ])

		| String s ->
			let s_arg = encode_string s in
			mk_singleton_elem (Expr.mk_app ctx lit_operations.string_constructor [ s_arg ])

		| Loc l ->
			let l_arg = encode_string l in
			mk_singleton_elem (Expr.mk_app ctx lit_operations.loc_constructor [ l_arg ])

		| Type t ->
			let t_arg = encode_type t in
			mk_singleton_elem (Expr.mk_app ctx lit_operations.type_constructor [ t_arg ])

		| LList lits ->
			let args = List.map (fun lit -> mk_singleton_access (encode_lit lit)) lits in
			let arg_list = mk_z3_list args list_operations.nil_constructor list_operations.cons_constructor in
			mk_singleton_elem (Expr.mk_app ctx lit_operations.list_constructor [ arg_list ])

	with (Failure msg) ->
		raise (Failure (Printf.sprintf "DEATH: encode_lit %s. %s" (JSIL_Print.string_of_literal lit false) msg))


(** Encode JSIL binary operators *)
let encode_binop op le1 le2 =

	let binop_numbers_to_numbers mk_op le1 le2 =
		let n_le1 = (Expr.mk_app ctx lit_operations.number_accessor [ (mk_singleton_access le1) ]) in
		let n_le2 = (Expr.mk_app ctx lit_operations.number_accessor [ (mk_singleton_access le2) ]) in
		let nle1_op_nle2 = mk_op n_le1 n_le2 in
		mk_singleton_elem (Expr.mk_app ctx lit_operations.number_constructor [ nle1_op_nle2 ]) in

	let binop_numbers_to_booleans mk_op le1 le2 =
		let n_le1 = (Expr.mk_app ctx lit_operations.number_accessor [ mk_singleton_access le1 ]) in
		let n_le2 = (Expr.mk_app ctx lit_operations.number_accessor [ mk_singleton_access le2 ]) in
		let nle1_op_nle2 = mk_op n_le1 n_le2 in
		mk_singleton_elem (Expr.mk_app ctx lit_operations.boolean_constructor [ nle1_op_nle2 ]) in

	match op with
	| Plus     -> binop_numbers_to_numbers mk_add le1 le2
	| Minus    -> binop_numbers_to_numbers mk_sub le1 le2
	| Times    -> binop_numbers_to_numbers mk_mul le1 le2
	| Div      -> binop_numbers_to_numbers mk_div le1 le2

	| LessThan      -> binop_numbers_to_booleans (mk_lt ctx) le1 le2
	| LessThanEqual -> binop_numbers_to_booleans (mk_le ctx) le1 le2


	| Equal    -> Expr.mk_app ctx lit_operations.boolean_constructor [ (Boolean.mk_eq ctx le1 le2) ]

	| LstCons  ->
		let le2_list = Expr.mk_app ctx lit_operations.list_accessor [ mk_singleton_access le2 ] in
		let new_list = Expr.mk_app ctx list_operations.cons_constructor [ mk_singleton_access le1; le2_list ] in
		mk_singleton_elem (Expr.mk_app ctx lit_operations.list_constructor [ new_list ])

	| SetMem ->
		let le1_mem = mk_singleton_access le1 in
		let le2_set = Expr.mk_app ctx extended_literal_operations.set_accessor [ le2 ] in
		let le      = Set.mk_membership ctx le1_mem le2_set in
		mk_singleton_elem (Expr.mk_app ctx lit_operations.boolean_constructor [ le ])

	| SetDiff ->
		let le1_set = Expr.mk_app ctx extended_literal_operations.set_accessor [ le1 ] in
		let le2_set = Expr.mk_app ctx extended_literal_operations.set_accessor [ le2 ] in
		let le      = Set.mk_difference ctx le1_set le2_set in
		Expr.mk_app ctx extended_literal_operations.set_constructor [ le ]

	| SetSub ->
		let le1_set = Expr.mk_app ctx extended_literal_operations.set_accessor [ le1 ] in
		let le2_set = Expr.mk_app ctx extended_literal_operations.set_accessor [ le2 ] in
		let le      = Set.mk_subset ctx le1_set le2_set in
		mk_singleton_elem (Expr.mk_app ctx lit_operations.boolean_constructor [ le ])

	| LstCat ->
		let n_le1 = (Expr.mk_app ctx lit_operations.list_accessor [ mk_singleton_access le1 ]) in
		let n_le2 = (Expr.mk_app ctx lit_operations.list_accessor [ mk_singleton_access le2 ]) in
		let n_le  = (Expr.mk_app ctx axiomatised_operations.lcat_fun [ n_le1; n_le2 ]) in
		mk_singleton_elem (Expr.mk_app ctx lit_operations.list_constructor [ n_le ])

	| _ -> raise (Failure "SMT encoding: Construct not supported yet - binop!")


let encode_unop op le =
	match op with

	| UnaryMinus ->
		let le_n    = Expr.mk_app ctx lit_operations.number_accessor [ mk_singleton_access le ] in
		let op_le_n = Arithmetic.mk_unary_minus ctx le_n in
		mk_singleton_elem (Expr.mk_app ctx lit_operations.number_constructor [ op_le_n ])

	| LstLen     ->
		let le_lst      = Expr.mk_app ctx lit_operations.list_accessor  [ mk_singleton_access le ] in
		let op_le_lst   = Expr.mk_app ctx axiomatised_operations.llen_fun [ le_lst ] in
		mk_singleton_elem (Expr.mk_app ctx lit_operations.number_constructor [ op_le_lst ])

	| StrLen     ->
		let le_s      = Expr.mk_app ctx lit_operations.string_accessor  [ mk_singleton_access le ] in
		let op_le_s   = Expr.mk_app ctx axiomatised_operations.slen_fun [ le_s ] in
		mk_singleton_elem (Expr.mk_app ctx lit_operations.number_constructor [ op_le_s ])

	| ToStringOp ->
		let le_n      = Expr.mk_app ctx lit_operations.number_accessor  [ mk_singleton_access le ] in
		let op_le_n   = Expr.mk_app ctx axiomatised_operations.num2str_fun [ le_n ] in
		mk_singleton_elem (Expr.mk_app ctx lit_operations.string_constructor [ op_le_n ])

	| ToNumberOp ->
		let le_s      = Expr.mk_app ctx lit_operations.string_accessor  [ mk_singleton_access le ] in
		let op_le_s   = Expr.mk_app ctx axiomatised_operations.str2num_fun [ le_s ] in
		mk_singleton_elem (Expr.mk_app ctx lit_operations.number_constructor [ op_le_s ])

	| ToIntOp    ->
		let le_n      = Expr.mk_app ctx lit_operations.number_accessor  [ mk_singleton_access le ] in
		let op_le_n   = Expr.mk_app ctx axiomatised_operations.num2int_fun [ le_n ] in
		mk_singleton_elem (Expr.mk_app ctx lit_operations.number_constructor [ op_le_n ])

	| Not        ->
		let le_b      = Expr.mk_app ctx lit_operations.boolean_accessor  [ mk_singleton_access le ] in
		let op_le_b	  = Boolean.mk_not ctx le_b in
		mk_singleton_elem (Expr.mk_app ctx lit_operations.boolean_constructor [ op_le_b ])

  	| Cdr ->
    	let le_lst      = Expr.mk_app ctx lit_operations.list_accessor  [ mk_singleton_access le ] in
    	let op_le_lst   = Expr.mk_app ctx list_operations.tail_accessor [ le_lst ] in
    	mk_singleton_elem (Expr.mk_app ctx lit_operations.list_constructor [ op_le_lst ])

    | Car ->
    	let le_lst      = Expr.mk_app ctx lit_operations.list_accessor  [ mk_singleton_access le ] in
    	let op_le       = Expr.mk_app ctx list_operations.head_accessor [ le_lst ] in
    	mk_singleton_elem op_le

	| _          ->
		Printf.printf "SMT encoding: Construct not supported yet - unop - %s!\n" (JSIL_Print.string_of_unop op);
		let msg = Printf.sprintf "SMT encoding: Construct not supported yet - unop - %s!" (JSIL_Print.string_of_unop op) in
		raise (Failure msg)


let rec encode_logical_expression le =

	let f = encode_logical_expression in

	match le with
	| LLit lit -> encode_lit lit

	| LNone    -> mk_singleton_elem (Expr.mk_app ctx lit_operations.none_constructor [])

	| LVar var -> Expr.mk_const ctx (mk_string_symb var) extended_literal_sort

	| ALoc var -> Expr.mk_const ctx (mk_string_symb var) extended_literal_sort

  | PVar var   -> raise (Failure (Printf.sprintf "Program variable %s in pure formula: FIRE" var))

	| LBinOp (le1, op, le2) -> encode_binop op (f le1) (f le2)

	| LUnOp (op, le) -> encode_unop op (f le)

	| LEList les ->
		let args = List.map (fun le -> mk_singleton_access (f le)) les in
		let arg_list = mk_z3_list args list_operations.nil_constructor list_operations.cons_constructor in
		mk_singleton_elem (Expr.mk_app ctx lit_operations.list_constructor [ arg_list ])

	| LLstNth (lst, index)  ->
	  let lst'   = Expr.mk_app ctx lit_operations.list_accessor  [ mk_singleton_access (f lst) ] in
		let msg    = Printf.sprintf "Failure - z3 encoding: Unsupported list indexing: %s" (JSIL_Print.string_of_logic_expression index false) in
		(match index with
		| LLit (Num index) ->
			(match (Utils.is_int index) with
			| false -> raise (Failure msg)
			| true -> 
					let index = int_of_float index in
					let index' = mk_int_i index in
					mk_singleton_elem (Expr.mk_app ctx axiomatised_operations.lnth_fun [ lst'; index' ]))
		| _ -> raise (Failure msg))

	| LStrNth (str, index)  ->
		let str'   = Expr.mk_app ctx lit_operations.string_accessor  [ mk_singleton_access (f str) ] in
		let msg    = Printf.sprintf "Failure - z3 encoding: Unsupported string indexing: %s" (JSIL_Print.string_of_logic_expression index false) in
		(match index with
		| LLit (Num index) ->
			(match (Utils.is_int index) with
			| false -> raise (Failure msg)
			| true -> 
					let index = int_of_float index in
					let index' = mk_int_i index in
					let res    = Expr.mk_app ctx axiomatised_operations.snth_fun [ str'; index' ] in
					mk_singleton_elem (Expr.mk_app ctx lit_operations.string_constructor [ res ]))
		| _ -> raise (Failure msg))
		
	| LTypeOf le ->
		let res = typeof_expression (f le) in
		mk_singleton_elem (Expr.mk_app ctx lit_operations.type_constructor [ res ])

	| LESet les ->
		let args = List.map (fun le -> mk_singleton_access (f le)) les in
		let arg_list = mk_z3_set args in
		Expr.mk_app ctx extended_literal_operations.set_constructor [ arg_list ]

	| LSetUnion les ->
		let le_set = List.map (fun le -> Expr.mk_app ctx extended_literal_operations.set_accessor [ f le ]) les in
		let le      = Set.mk_union ctx le_set in
		Expr.mk_app ctx extended_literal_operations.set_constructor [ le ]

	| LSetInter les ->
		let le_set = List.map (fun le -> Expr.mk_app ctx extended_literal_operations.set_accessor [ f le ]) les in
		let le      = Set.mk_intersection ctx le_set in
		Expr.mk_app ctx extended_literal_operations.set_constructor [ le ]

	| _                     ->
		let msg = Printf.sprintf "Failure - z3 encoding: Unsupported logical expression: %s"
			(JSIL_Print.string_of_logic_expression le false) in
		raise (Failure msg)



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



let global_axioms = []

	(* forall x. slen(x) >= 0 
	let x    = "x" in
	let le_x = mk_const_i (mk_string_symb x) in
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
	let a1        = Boolean.mk_eq ctx le_x (Expr.mk_app ctx list_operations.nil_constructor []) in
	let le_llen_x = Expr.mk_app ctx axiomatised_operations.llen_fun [ le_x ] in
	let a2        = mk_lt ctx (mk_num_i 0) le_llen_x in
	let a         = Boolean.mk_or ctx [a1; a2] in
	let llen_axiom2 = encode_quantifier true ctx [ x ] [ z3_jsil_list_sort ] a in

	[ slen_axiom; llen_axiom1; llen_axiom2 ] *)

let make_recognizer_assertion x t_x =
	let le_x = Expr.mk_const ctx (mk_string_symb x) extended_literal_sort in

	let non_set_type_recognizer f =
		let a1 = Expr.mk_app ctx extended_literal_operations.singular_elem_recognizer [ le_x ] in
		let a2 = Expr.mk_app ctx f  [ mk_singleton_access le_x ] in
		Boolean.mk_and ctx [ a1; a2 ] in

	match t_x with
	| UndefinedType -> non_set_type_recognizer lit_operations.undefined_recognizer
	| NullType      -> non_set_type_recognizer lit_operations.null_recognizer
	| EmptyType     -> non_set_type_recognizer lit_operations.empty_recognizer
	| NoneType      -> non_set_type_recognizer lit_operations.none_recognizer
	| BooleanType   -> non_set_type_recognizer lit_operations.boolean_recognizer
	| NumberType    -> non_set_type_recognizer lit_operations.number_recognizer
	| CharType	    -> non_set_type_recognizer lit_operations.char_recognizer
	| StringType    -> non_set_type_recognizer lit_operations.string_recognizer
	| ObjectType    -> non_set_type_recognizer lit_operations.loc_recognizer
	| ListType      -> non_set_type_recognizer lit_operations.list_recognizer
	| TypeType      -> non_set_type_recognizer lit_operations.type_recognizer
	| SetType       -> Expr.mk_app ctx extended_literal_operations.set_recognizer [ le_x ]



let rec encode_assertion a : Expr.expr =

	(* print_time_debug "EPF:"; *)
	let f = encode_assertion in
	let fe = encode_logical_expression in

	match a with
	| LNot a             -> Boolean.mk_not ctx (f a)
	| LEq (le1, le2)     -> Boolean.mk_eq ctx (fe le1) (fe le2)
	| LLess (le1, le2)   ->
		let le1' = Expr.mk_app ctx lit_operations.number_accessor  [ mk_singleton_access (fe le1) ] in
		let le2' = Expr.mk_app ctx lit_operations.number_accessor  [ mk_singleton_access (fe le2) ] in
		mk_lt ctx le1' le2'
	| LLessEq (le1, le2) ->
		let le1' = Expr.mk_app ctx lit_operations.number_accessor  [ mk_singleton_access (fe le1) ] in
		let le2' = Expr.mk_app ctx lit_operations.number_accessor  [ mk_singleton_access (fe le2) ] in
		mk_le ctx le1' le2'
	| LStrLess (_, _)    -> raise (Failure ("Z3 encoding does not support STRLESS"))
	| LTrue	             -> Boolean.mk_true ctx
	| LFalse             -> Boolean.mk_false ctx
	| LOr (a1, a2)       -> Boolean.mk_or ctx [ (f a1); (f a2) ]
	| LAnd (a1, a2)      -> Boolean.mk_and ctx [ (f a1); (f a2) ]
	| LSetMem (le1, le2) ->
		let le1' = mk_singleton_access (fe le1) in
		let le2' = Expr.mk_app ctx extended_literal_operations.set_accessor  [ fe le2 ] in
		Set.mk_membership ctx le1' le2'
	| LSetSub (le1, le2) ->
		let le1' = Expr.mk_app ctx extended_literal_operations.set_accessor  [ fe le1 ] in
		let le2' = Expr.mk_app ctx extended_literal_operations.set_accessor  [ fe le2 ] in
		Set.mk_subset ctx le1' le2'

	| LForAll (bt, a) ->
			let binders, types = List.split bt in
			let z3_sorts = List.map (fun x -> extended_literal_sort) binders in
			let z3_types_assertions = List.map (fun (x, t_x) -> make_recognizer_assertion x t_x) bt in
			let z3_types_assertion = Boolean.mk_and ctx z3_types_assertions in
			let z3_a  = Boolean.mk_implies ctx z3_types_assertion (f a) in
			encode_quantifier true ctx binders z3_sorts z3_a

	| _ ->
		let msg = Printf.sprintf "Unsupported assertion to encode for Z3: %s" (JSIL_Print.string_of_logic_assertion a false) in
		raise (Failure msg)


let encode_assertion_top_level a = encode_assertion (JSIL_Logic_Utils.push_in_negations_off a)

let encode_gamma gamma =
	let gamma_var_type_pairs = get_gamma_var_type_pairs gamma in
	let encoded_gamma =
		List.filter
			(fun x -> x <> Boolean.mk_true ctx)
			(List.map
				(fun (x, t_x) ->
					if ((is_lvar_name x) || (is_abs_loc_name x))
						then make_recognizer_assertion x t_x
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

let print_model solver =
	let model = Solver.get_model solver in
	match model with
	| Some model ->
		let str_model = Model.to_string model in
		print_debug (Printf.sprintf "I found the model: \n\n%s" str_model)
	| None ->
		print_debug ("No model found.")

let string_of_solver solver =
	let exprs = Solver.get_assertions solver in
	string_of_z3_expr_list exprs


let make_global_axioms list_vars string_vars list_exprs =
	let x_name = "#x" in
	let y_name = "#y" in
	let lvar_x = LVar x_name in
	let lvar_y = LVar y_name in

  	(* forall x. 0 <= slen(x) *)
	let slen1 = LLessEq (LLit (Num 0.), LUnOp (StrLen, lvar_x)) in
	let slen1_s = JSIL_Logic_Utils.concretise slen1 x_name string_vars in

	(* forall x. 0 <= llen(x) *)
	let llen1 = LLessEq (LLit (Num 0.), LUnOp (LstLen, lvar_x)) in
  let llen1_s = JSIL_Logic_Utils.concretise llen1 x_name list_vars in

	(* forall x. (x = nil) \/ (0 < llen(x))
	(LLess ((LLit (Num 0.), LUnop (LstLen, lvar_x)))) *)
	let llen2 =
		LOr (LEq (lvar_x, LLit (LList [])),
		 	 LLess (LLit (Num 0.), LUnOp (LstLen, lvar_x))) in
 let llen2_s = JSIL_Logic_Utils.concretise llen2 x_name list_vars in

	(* forall x. (car(x) = l-nth(x, 0) *)
	let carlnth0 = LEq (LUnOp (Car, lvar_x), LLstNth (lvar_x, LLit (Num 0.))) in
	let carlnth0_s = JSIL_Logic_Utils.concretise carlnth0 x_name list_vars in

	(* forall x, y. ((x = nil) /\ (y = nil)) \/ (! (x @ y = nil)) 
	let l_disjunct = LAnd (LEq (lvar_x, LLit (LList [])), LEq (lvar_y, LLit (LList []))) in
	let r_disjunct = LNot (LEq (LLit (LList []), LBinOp (lvar_x, LstCat, lvar_y))) in
	let lstcat1    = LOr (l_disjunct, r_disjunct) in
	let lstcat1_s  = JSIL_Logic_Utils.concretise2 lstcat1 x_name y_name list_exprs in *)

	slen1_s @ llen1_s @ llen2_s @ carlnth0_s 

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


let make_relevant_axioms a list_vars string_vars list_exprs =
	(* string axioms *)
	let a_strings, _ = JSIL_Logic_Utils.get_assertion_string_number_literals a in
	let a_strings    = JSIL_Logic_Utils.remove_string_duplicates a_strings in
	let s_axioms     = List.concat (List.map make_string_axioms a_strings) in

	(* list axioms *)
	let a_lists      = JSIL_Logic_Utils.get_assertion_lists a in
	let l_axioms     = List.concat (List.map make_list_axioms a_lists) in

	let constant_axioms = make_global_axioms list_vars string_vars list_exprs in

	(*if (List.length l_axioms > 0) then *)

	print_debug_petar (Printf.sprintf "Generated Axioms:\n%s\n"
	   (Symbolic_State_Print.string_of_shallow_p_formulae (DynArray.of_list (l_axioms @ constant_axioms)) false));

	s_axioms @ l_axioms @ constant_axioms

(** ****************
  * SATISFIABILITY *
	* **************** **)
let check_satisfiability assertions gamma =
	let start_time = Sys.time () in

	let new_assertions, new_gamma = Simplifications.simplify_pfs (DynArray.of_list assertions) gamma None in

	let new_assertions_set = SA.of_list (DynArray.to_list new_assertions) in
	let new_assertions = SA.elements new_assertions_set in
	let cache_assertion = star_asses new_assertions in

	print_debug_petar (Printf.sprintf "About to check sat of:\nPure formulae:\n%s\nGamma:\n%s\n\n"
			(Symbolic_State_Print.string_of_shallow_p_formulae (DynArray.of_list new_assertions) false)
			(Symbolic_State_Print.string_of_gamma new_gamma));

	if (Hashtbl.mem JSIL_Syntax.check_sat_cache cache_assertion) then
	begin
		let ret = Hashtbl.find JSIL_Syntax.check_sat_cache cache_assertion in
		let end_time = Sys.time() in
		JSIL_Syntax.update_statistics "check_satisfiability" (end_time -. start_time);
		JSIL_Syntax.update_statistics "sat_cache" 0.;
		print_debug_petar (Printf.sprintf "Found in cache. Cache length %d." (Hashtbl.length JSIL_Syntax.check_sat_cache));
		ret
	end
	else
	begin
		print_debug_petar (Printf.sprintf "Not found in cache. Cache length %d." (Hashtbl.length JSIL_Syntax.check_sat_cache));
		let solver = get_new_solver new_assertions new_gamma in
		print_debug_petar (Printf.sprintf "SAT: About to check the following:\n%s" (string_of_solver solver));
		let ret = Solver.check solver [] in
		print_debug (Printf.sprintf "The solver returned: %s"
			(match ret with
			| Solver.SATISFIABLE -> "SAT"
			| Solver.UNSATISFIABLE -> "UNSAT"
			| Solver.UNKNOWN -> "UNKNOWN"));
		let ret = (ret = Solver.SATISFIABLE) in
		Hashtbl.add JSIL_Syntax.check_sat_cache cache_assertion ret;
		print_debug_petar (Printf.sprintf "Adding %s to cache. Cache length %d."
			(JSIL_Print.string_of_logic_assertion cache_assertion false) (Hashtbl.length JSIL_Syntax.check_sat_cache));
		let end_time = Sys.time () in
		JSIL_Syntax.update_statistics "solver_call" 0.;
		JSIL_Syntax.update_statistics "check_satisfiability" (end_time -. start_time);
		ret
	end

(** ************
  * ENTAILMENT *
	* ************ **)
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

		let start_time = Sys.time () in

		let existentials, left_as, right_as, gamma =
			Simplifications.simplify_implication existentials (DynArray.of_list left_as) (DynArray.of_list right_as) (copy_gamma gamma) in
		let right_as = Simplifications.simplify_equalities_between_booleans right_as in
			Simplifications.filter_gamma_pfs (DynArray.of_list (DynArray.to_list left_as @ DynArray.to_list right_as)) gamma;

		(* If right is empty, then the left only needs to be satisfiable *)
		if (DynArray.empty right_as) then (
			let result = check_satisfiability (DynArray.to_list left_as) gamma in
			let end_time = Sys.time () in
				JSIL_Syntax.update_statistics "check_entailment" (end_time -. start_time);
			result
			) else
		(* If left or right are directly false, everything is false *)
		if (DynArray.get right_as 0 = LFalse || (DynArray.length left_as <> 0 && DynArray.get left_as 0 = LFalse)) then (
			let result = check_satisfiability (DynArray.to_list left_as) gamma in
			let end_time = Sys.time () in
				JSIL_Syntax.update_statistics "check_entailment" (end_time -. start_time);
			false
		) else (
		let list_vars   = List.map (fun x -> LVar x) (get_vars_of_type gamma ListType) in
		let string_vars = List.map (fun x -> LVar x) (get_vars_of_type gamma StringType) in
		let list_exprs  : jsil_logic_expr list = List.concat (List.map JSIL_Logic_Utils.get_list_exprs ((DynArray.to_list left_as) @ (DynArray.to_list right_as))) in
		let list_exprs  = list_exprs @ list_vars in

		let left_as = DynArray.to_list left_as in
		let right_as = DynArray.to_list right_as in

		let gamma_left  = filter_gamma_f gamma (fun v -> not (SS.mem v existentials)) in
		let gamma_right = filter_gamma_f gamma (fun v -> SS.mem v existentials) in

		let left_as_axioms =
			List.concat
				(List.map (fun a -> make_relevant_axioms a list_vars string_vars list_exprs) left_as) in
		let left_as = List.map encode_assertion_top_level (left_as_axioms @ left_as) in
		let left_as = global_axioms @ (encode_gamma gamma_left) @ left_as in
		let solver = (Solver.mk_solver ctx None) in
		Solver.add solver left_as;
		print_debug_petar (Printf.sprintf "ENT ENCODED: About to check the following:\n%s" (string_of_solver solver));
		let ret_left = (Solver.check solver [ ] = Solver.SATISFIABLE) in
		if (ret_left) then (
			let right_as_axioms =
				List.concat
					(List.map (fun a -> make_relevant_axioms a list_vars string_vars list_exprs) right_as) in
			let right_as_axioms = List.map encode_assertion_top_level right_as_axioms in
			let right_as = List.map (fun a -> encode_assertion_top_level (LNot a)) right_as in
			let right_as_or =
				if ((List.length right_as) > 1) then
						(Boolean.mk_or ctx right_as)
					else if ((List.length right_as) = 1) then
						(List.nth right_as 0)
					else Boolean.mk_false ctx in

			let existentials = SS.elements existentials in
			let existentials_sorts = List.map (fun _ -> extended_literal_sort) existentials in
			let right_as_or =
				print_debug_petar (Printf.sprintf "Length of existentials: %d" (List.length existentials));
				if ((List.length existentials) > 0)
					then (
						let a_gamma_right   = encode_gamma gamma_right in
						let a_right         = Boolean.mk_and ctx ( right_as_or :: a_gamma_right ) in
						encode_quantifier true ctx existentials existentials_sorts a_right
					) else right_as_or in

			Solver.add solver (right_as_or :: right_as_axioms);
			print_debug_petar (Printf.sprintf "ENT: About to check the following:\n%s" (string_of_solver solver));

			let ret = Solver.check solver [ ] in
			print_debug_petar (Printf.sprintf "The solver returned: %s"
						(match ret with
						| Solver.SATISFIABLE -> "SAT"
						| Solver.UNSATISFIABLE -> "UNSAT"
						| Solver.UNKNOWN -> "UNKNOWN"));
			let end_time = Sys.time () in
			JSIL_Syntax.update_statistics "solver_call" 0.;
			JSIL_Syntax.update_statistics "check_entailment" (end_time -. start_time);

			if (ret = Solver.SATISFIABLE) then print_model solver;
			let ret = (ret = Solver.UNSATISFIABLE) in
			ret)
		else (
			print_time_debug ("check_entailment done: false. OUTER");
			false))


let is_equal_on_lexprs e1 e2 pfs : bool option =
(match (e1 = e2) with
(* This true check is not good enough, things could creep in with Unknowns *)
| true -> Some true
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
