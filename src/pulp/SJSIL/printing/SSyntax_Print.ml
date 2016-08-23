open SJSIL_Lexer
open SSyntax
open SSyntax_Aux

(***
 S-Expression Serialization
*)
let string_of_float x = 
	if (x == nan) 
		then "nan"
		else if (x == neg_infinity) 
						then "-inf"
						else if (x == infinity) 
									then "inf"
									else string_of_float x 

let is_int v =
  v = (snd (modf v))

let sexpr_of_float x = 
	if (x == nan) 
		then "+nan.0"
		else if (x == neg_infinity) 
						then "-inf.0"
						else if (x == infinity) 
									then "+inf.0"
									else
										if (is_int x) 
											then string_of_int (int_of_float x) 
											else string_of_float x 
									
(**	
the following does not work because nan is interpreted as a variable
 match x with 
	| nan -> "+nan.0"
	| neg_infinity -> "-inf.0"
	| infinity -> "+inf.0"
	| _ -> string_of_float x
*)

let string_of_binop bop = match bop with 
  | Equal -> binop_eq
  | LessThan -> binop_lt
	| LessThanString -> binop_lts
  | LessThanEqual -> binop_leq
 	| Plus -> binop_plus
  | Minus -> binop_minus
  | Times -> binop_times
  | Div -> binop_div
  | Mod -> binop_mod
	| Subtype -> binop_subtype
	| Concat -> binop_concat
	| Append -> binop_append
	| And -> binop_and
  | Or -> binop_or
	| BitwiseAnd -> binop_band
  | BitwiseOr -> binop_bor
  | BitwiseXor -> binop_bxor
  | LeftShift -> binop_lsh
  | SignedRightShift -> binop_srsh
  | UnsignedRightShift -> binop_ursh
	| LCons -> binop_lcons
	| M_atan2 -> binop_atan2
	| M_pow -> binop_pow

let sexpr_of_binop bop = match bop with 
  | Equal -> binop_eq
  | LessThan -> binop_lt
	| LessThanString -> binop_lts
  | LessThanEqual -> binop_leq
 	| Plus -> binop_plus
  | Minus -> binop_minus
  | Times -> binop_times
  | Div -> binop_div
  | Mod -> binop_mod
	| Subtype -> binop_subtype
	| Concat -> binop_concat
	| Append -> binop_append
	| And -> binop_and
  | Or -> binop_or
	| BitwiseAnd -> binop_band
  | BitwiseOr -> "bor"
  | BitwiseXor -> binop_bxor
  | LeftShift -> binop_lsh
  | SignedRightShift -> binop_srsh
  | UnsignedRightShift -> binop_ursh
	| LCons -> binop_lcons
	| M_atan2 -> binop_atan2
	| M_pow -> binop_pow

let string_of_unop uop = match uop with 
  | Not -> unop_not
  | Negative -> unop_neg
	| ToStringOp -> unop_tostr
  | ToNumberOp -> unop_tonum
  | ToIntOp -> unop_toint
	| ToInt32Op -> unop_toint32
  | ToUint16Op -> unop_touint16
  | ToUint32Op -> unop_touint32
  | BitwiseNot -> unop_bnot
	| Car -> unop_car
	| Cdr -> unop_cdr
	| IsPrimitive -> unop_isprim
	| Length -> unop_len
	| M_abs -> unop_abs            
	| M_acos -> unop_acos         
	| M_asin -> unop_asin      
	| M_atan -> unop_atan    
	| M_ceil -> unop_ceil            
	| M_cos -> unop_cos    
	| M_exp -> unop_exp         
	| M_floor -> unop_floor          
	| M_log -> unop_log    
	| M_round -> unop_round  
	| M_sgn -> unop_sgn     
	| M_sin -> unop_sin            
	| M_sqrt -> unop_sqrt          
	| M_tan -> unop_tan          
	
let string_of_bool x =
  match x with
    | true -> "$$t"
    | false -> "$$f"

let sexpr_of_bool x =
  match x with
    | true -> "#t"
    | false -> "#f"

let string_of_type t =
  match t with
  | NullType -> "$$null_type"
  | UndefinedType -> "$$undefined_type"
  | BooleanType -> "$$boolean_type"
  | StringType -> "$$string_type"
  | NumberType -> "$$number_type"
	| IntType -> "$$int_type"
  | ObjectType -> "$$object_type"
  | ReferenceType -> "$$reference_type"
	| ObjectReferenceType -> "$$o-reference_type"
	| VariableReferenceType -> "$$v-reference_type"	
	| EmptyType -> "$$empty_type"
	| TypeType -> "$$type_type"
	| ListType -> "$$list_type"
		
let string_of_constant c =
	match c with
	| Min_float -> "$$min_value"
	| Max_float -> "$$max_value"
	| Random -> "$$random"
	| E -> "$$e"
	| Ln10 -> "$$ln10"
	| Ln2 -> "$$ln2"
	| Log2e -> "$$log2e"
	| Log10e -> "$$log10e"
	| Pi -> "$$pi"
	| Sqrt1_2 -> "$$sqrt1_2"
	| Sqrt2 -> "$$sqrt2"
		
let rec string_of_literal lit escape_string =
  match lit with
	  | Undefined -> "$$undefined"
	  | Null -> "$$null"
	  | Empty -> "$$empty" 
		| Loc loc -> loc
    | Num n -> string_of_float n
    | String x -> 
				if escape_string 
					then Printf.sprintf "\\\"%s\\\"" x
					else Printf.sprintf "\"%s\"" x
    | Bool b -> string_of_bool b
    | Type t -> string_of_type t 
		| LVRef (l, x) -> Printf.sprintf "%s.v.%s" (string_of_literal l escape_string) x  
	  | LORef (l, x) -> Printf.sprintf "%s.o.%s" (string_of_literal l escape_string) x   
		| LList ll -> 
			(match ll with
			| [] -> "$$nil"
			| ll ->
			let rec loop ll = 
				(match ll with
				| [] -> ""
				| lit :: ll -> 
					let scar = string_of_literal lit escape_string in
					let ssep = 
						(match ll with
						| [] -> ""
						| _ -> ", ") in
					let scdr = loop ll in
					Printf.sprintf ("%s%s%s") scar ssep scdr)
			in Printf.sprintf "{{ %s }}" (loop ll))
		| Constant c -> string_of_constant c 

let rec sexpr_of_literal lit =
  match lit with
	  | Undefined -> "$$undefined"
	  | Null -> "$$null"
	  | Empty -> "$$empty" 
		| Loc loc -> loc
    | Num n -> sexpr_of_float n
    | String x -> Printf.sprintf "\"%s\"" x
    | Bool b -> sexpr_of_bool b
    | Type t -> string_of_type t 
		| LVRef (l, x) -> Printf.sprintf "(ref %s \"%s\" $$v-reference_type)" (sexpr_of_literal l) x  
	  | LORef (l, x) -> Printf.sprintf "(ref %s \"%s\" $$o-reference_type)" (sexpr_of_literal l) x   
		| LList ll -> 
			(match ll with
			| [] -> "(jsil-list )"
			| ll ->
			let rec loop ll = 
				(match ll with
				| [] -> ""
				| lit :: ll -> 
					let scar = sexpr_of_literal lit in
					let ssep = 
						(match ll with
						| [] -> ""
						| _ -> " ") in
					let scdr = loop ll in
					Printf.sprintf ("%s%s%s") scar ssep scdr)
			in Printf.sprintf "(jsil-list %s )" (loop ll))
		| Constant c -> string_of_constant c 

let fresh_sth (name : string) : (unit -> string) =
  let counter = ref 0 in
  let rec f () =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f
  
let fresh_symbol : (unit -> string) = fresh_sth "symb_"

let rec sexpr_of_expression e =
  let se = sexpr_of_expression in
  match e with
    | Literal l -> sexpr_of_literal l
    | Var v -> Pulp_Syntax_Print.string_of_var v
		(* (bop e1 e2) *)
    | BinOp (e1, op, e2) -> Printf.sprintf "(%s %s %s)" (sexpr_of_binop op) (se e1) (se e2)
		(* (uop e1 e2) *)
    | UnaryOp (op, e) -> Printf.sprintf "(%s %s)" (string_of_unop op) (se e)
		(* (typeof e) *)
    | TypeOf e -> Printf.sprintf "(typeof %s)" (se e) 
		(* (ref-v e1 e2) *)
    | VRef (e1, e2) -> Printf.sprintf "(ref-v %s %s)" (se e1) (se e2)
  	(* (ref-o e1 e2) *)
    | ORef (e1, e2) -> Printf.sprintf "(ref-o %s %s)" (se e1) (se e2)
		(* (base e) *)
    | Base e -> Printf.sprintf "(base %s)" (se e)
		(* (field e) *)
    | Field e -> Printf.sprintf "(field %s)" (se e)
		(* (s-nth e n) *)
		| SNth (e1, e2) -> Printf.sprintf "(s-nth %s %s)" (se e1) (se e2)
		(* (l-nth e n) *)
		| LNth (e1, e2) -> Printf.sprintf "(l-nth %s %s)" (se e1) (se e2)
		(* (jsil-list sexpr-e1 ... sexpr-en) *) 
		| EList ll -> 
			(match ll with
			| [] -> "(jsil-list )"
			| ll ->
			let rec loop ll = 
				(match ll with
				| [] -> ""
				| e :: ll -> 
					let scar = sexpr_of_expression e in
					let ssep = 
						(match ll with
						| [] -> ""
						| _ -> " ") in
					let scdr = loop ll in
					Printf.sprintf ("%s%s%s") scar ssep scdr)
			in Printf.sprintf "(jsil-list %s)" (loop ll))
		(* (jsil-cons e, e) *)
		| Cons (e1, e2) -> 
			Printf.sprintf "(jsil-cons %s %s)" (se e1) (se e2) 
		(* (assume e) *) 
		| RAssume e -> Printf.sprintf "(assume %s)" (se e)
		(* (assert e) *)
		| RAssert e -> Printf.sprintf "(assert %s)" (se e)
		(* (make-symbol-number) *) 
		| RNumSymb -> 
			let x = fresh_symbol () in 
			Printf.sprintf "(make-symbol-number %s)" x 
		(* (make-symbol-string) *) 
		| RStrSymb -> 
			let x = fresh_symbol () in 
			Printf.sprintf "(make-symbol-string %s)" x


let rec string_of_expression e escape_string =
  let se = fun e -> string_of_expression e escape_string in
  match e with
    | Literal l -> string_of_literal l escape_string
    | Var v -> Pulp_Syntax_Print.string_of_var v
		(* (e1 bop e2) *)
    | BinOp (e1, op, e2) -> Printf.sprintf "(%s %s %s)" (se e1) (string_of_binop op) (se e2)
		(* (uop e) *)
    | UnaryOp (op, e) -> Printf.sprintf "(%s %s)" (string_of_unop op) (se e)
		(* (typeof e) *)
    | TypeOf e -> Printf.sprintf "typeOf(%s)" (se e)
		(* ('ref-v e1 e2) *)
    | VRef (e1, e2) -> Printf.sprintf "v-ref(%s, %s)" (se e1) (se e2)
  	(* ('ref-o e1 e2) *)
    | ORef (e1, e2) -> Printf.sprintf "o-ref(%s, %s)" (se e1) (se e2)
		(* ('base e) *)
    | Base e -> Printf.sprintf "base(%s)" (se e)
		(* ('field e) *)
    | Field e -> Printf.sprintf "field(%s)" (se e)
		(* ('s-nth e n) *)
		| SNth (e1, e2) -> Printf.sprintf "s-nth(%s, %s)" (se e1) (se e2)
		(* ('l-nth e n) *)
		| LNth (e1, e2) -> Printf.sprintf "l-nth(%s, %s)" (se e1) (se e2)
		(* *)
		| EList ll -> 
			(match ll with
			| [] -> "$$nil"
			| ll ->
			let rec loop ll = 
				(match ll with
				| [] -> ""
				| e :: ll -> 
					let scar = string_of_expression e escape_string in
					let ssep = 
						(match ll with
						| [] -> ""
						| _ -> ", ") in
					let scdr = loop ll in
					Printf.sprintf ("%s%s%s") scar ssep scdr)
			in Printf.sprintf "{{ %s }}" (loop ll))
		(* cons(e, e) *)
		| Cons (e1, e2) -> 
			Printf.sprintf "cons(%s, %s)" (se e1) (se e2) 
		(* (assume e) *) 
		| RAssume e -> Printf.sprintf "assume(%s)" (se e)
		(* (assert e) *)
		| RAssert e -> Printf.sprintf "assert(%s)" (se e)
		(* (make-symbol-number) *) 
		| RNumSymb -> "make-symbol-number()" 
		(* (make-symbol-string) *) 
		| RStrSymb -> "make-symbol-string()"

let rec sexpr_of_bcmd bcmd i line_numbers_on = 
	let se = sexpr_of_expression in
	let str_i = if line_numbers_on then (string_of_int i) ^ " " else "" in
	match bcmd with 
	(* ('skip) *)
  | SSkip -> Printf.sprintf "'(%sskip)" str_i
	(* ('var_assign var e) *)
	| SAssignment (var, e) -> Printf.sprintf "'(%sv-assign %s %s)" str_i var (se e)
	(* ('new var) *)
	| SNew var -> Printf.sprintf "'(%snew %s)" str_i var
 	(* ('h-read var e1 e2)	*)
	| SLookup (var, e1, e2) -> Printf.sprintf "'(%sh-read %s %s %s)" str_i var (se e1) (se e2)
	(* ('h-assign var e e) *)
	| SMutation (e1, e2, e3) -> Printf.sprintf "'(%sh-assign %s %s %s)" str_i (se e1) (se e2) (se e3)
	(* ('delete var e1 e2) *)
	| SDelete (e1, e2) ->  Printf.sprintf "'(%sh-delete %s %s)" str_i (se e1) (se e2)	
	(* ('has-field var e1 e2) *)
  | SHasField (var, e1, e2) -> Printf.sprintf "'(%shas-field %s %s %s)" str_i var (se e1) (se e2)
  (* ('get-fields var e) *)
	| SGetFields (var, e) -> Printf.sprintf "'(%sget-fields %s %s)" str_i var (se e)
	| SArguments (var) -> Printf.sprintf "'(%sarguments %s)" str_i var

let rec string_of_bcmd bcmd i line_numbers_on escape_string = 
	let se = fun e -> string_of_expression e escape_string in
	let str_i = if line_numbers_on then (string_of_int i) ^ ". " else "" in
	match bcmd with 
	(* skip *)
  | SSkip -> Printf.sprintf "%sskip" str_i
	(* var := e *)
	| SAssignment (var, e) -> Printf.sprintf "%s%s := %s" str_i var (se e)					
	(* x := new() *)
	| SNew var -> Printf.sprintf "%s%s := new()" str_i var
 	(* x := [e1, e2]	*)
	| SLookup (var, e1, e2) -> Printf.sprintf "%s%s := [%s, %s]" str_i var (se e1) (se e2)
	(* [e1, e2] := e3 *)
	| SMutation (e1, e2, e3) -> Printf.sprintf "%s[%s, %s] := %s" str_i (se e1) (se e2) (se e3)
	(* delete(e1, e2) *)
	| SDelete (e1, e2) ->  Printf.sprintf "%sdelete(%s,%s)" str_i (se e1) (se e2)	
	(* x := hasField(e1, e2) *)
  | SHasField (var, e1, e2) -> Printf.sprintf "%s%s := hasField(%s,%s)" str_i var (se e1) (se e2)
	(* x := getFields (e1, e2) *)
	| SGetFields (var, e) -> Printf.sprintf "%s%s := getFields (%s)" str_i var (se e) 	
	(* x := args *)
	| SArguments var -> Printf.sprintf "%s%s := args" str_i var

let rec sexpr_of_cmd sjsil_cmd tabs i line_numbers_on =
	let sjsil_cmd = match sjsil_cmd with | (_, cmd) -> cmd in
	let str_i = if line_numbers_on then (string_of_int i) ^ " " else "" in
	let str_tabs = tabs_to_str tabs in  
  match sjsil_cmd with
	(* ('goto j) *) 
  | SGoto j -> 
		let str_j = string_of_int j in 
			str_tabs ^ Printf.sprintf "'(%sgoto %s)" str_i str_j 
  (* ('goto e j k) *)
	| SGuardedGoto (e, j, k) -> 
		let str_j = string_of_int j in
		let str_k = string_of_int k in
		let str_e = (sexpr_of_expression e) in 
			str_tabs ^  Printf.sprintf "'(%sgoto %s %s %s)" str_i str_e str_j str_k
	(* basic command *)
	| SBasic bcmd -> str_tabs ^ sexpr_of_bcmd bcmd i line_numbers_on
	(* ('call left_var proc_name '(arg1 ... argn) err_lab) *)
	| SCall (var, proc_name_expr, arg_expr_list, error_lab) -> 
		let proc_name_expr_str = sexpr_of_expression proc_name_expr in 
		let error_lab = (match error_lab with | None -> "" | Some error_lab -> (string_of_int error_lab)) in 
		let arg_expr_list_str = match arg_expr_list with
		|	[] -> ""
		| _ -> String.concat " " (List.map sexpr_of_expression arg_expr_list) in 
			str_tabs ^  Printf.sprintf "'(%scall %s %s (%s) %s)" str_i var proc_name_expr_str arg_expr_list_str error_lab
	(* ('v-phi-assign var var_1 var_2 ... var_n) *)
	| SPhiAssignment (var, var_arr) -> 
		let var_arr_str = 
			Array.fold_left 
				(fun ac v -> 
					match v with 
					| Some v -> ac ^ " " ^ v
					| None -> ac ^ " $$empty "
				)
				""
				var_arr in 
		str_tabs ^ (Printf.sprintf "'(%sv-phi-assign %s %s)" str_i var var_arr_str)
	(* ('v-psi-assign var var_1 var_2 ... var_n) *)
	| SPsiAssignment(var, var_arr) -> 
		let var_arr_str = 
			Array.fold_left 
				(fun ac v -> 
					match v with 
					| Some v -> ac ^ " " ^ v
					| None -> ac ^ " $$empty "
				)
				""
				var_arr in 
		str_tabs ^ (Printf.sprintf "'(%sv-psi-assign %s %s)" str_i var var_arr_str)	
	(* ('apply left_var expr_list err_lab) *)
	| SApply (var, arg_expr_list, error_lab) ->
		let error_lab = (match error_lab with | None -> "" | Some error_lab -> (string_of_int error_lab)) in 
		let arg_expr_list_str = match arg_expr_list with
		|	[] -> ""
		| _ -> String.concat " " (List.map sexpr_of_expression arg_expr_list) in 
			str_tabs ^  Printf.sprintf "'(%sapply %s (%s) %s)" str_i var arg_expr_list_str error_lab


let sexpr_of_params fparams =
	match fparams with
	| [] -> ""
	| param :: rest ->
  	List.fold_left 
  		(fun prev_params param -> prev_params ^ " '" ^ param)  (" '" ^ param) rest

let string_of_params fparams =
	match fparams with
	| [] -> ""
	| param :: rest ->
  	List.fold_left 
  		(fun prev_params param -> prev_params ^ ", " ^ param) param rest

let rec string_of_lexpression lexpr escape_string = 
	(match lexpr with
	| LLit l -> string_of_literal l escape_string
	| LNone -> "none"
	| LVar var -> var	
	| ALoc var -> var
	| PVar var -> var
	| LBinOp (lexpr1, binop, lexpr2) -> (string_of_lexpression lexpr1 escape_string) ^ " " ^ (string_of_binop binop) ^ " " ^ (string_of_lexpression lexpr2 escape_string)
	| LUnOp (unop, lexpr1) -> (string_of_unop unop) ^ " " ^ (string_of_lexpression lexpr1 escape_string)
	| LEVRef (lexpr1, lexpr2) -> "v-ref(" ^ (string_of_lexpression lexpr1 escape_string) ^ ", " ^ (string_of_lexpression lexpr2 escape_string) ^ ")"
	| LEORef (lexpr1, lexpr2) -> "o-ref(" ^ (string_of_lexpression lexpr1 escape_string) ^ ", " ^ (string_of_lexpression lexpr2 escape_string) ^ ")"
	| LBase lexpr1 -> "base(" ^ (string_of_lexpression lexpr1 escape_string) ^ ")"
	| LField lexpr1 -> "field(" ^ (string_of_lexpression lexpr1 escape_string) ^ ")"
	| LTypeOf lexpr1 -> "typeOf(" ^ (string_of_lexpression lexpr1 escape_string) ^ ")"
	)
	
let rec string_of_assertion lass escape_string = 
	  (match lass with
	   | LAnd	(lass1, lass2) -> (string_of_assertion lass1 escape_string) ^ " /\\ " ^ (string_of_assertion lass2 escape_string)
	   | LOr (lass1, lass2) ->	(string_of_assertion lass1 escape_string) ^ " \\/ " ^ (string_of_assertion lass2 escape_string)
	   | LNot	lass1 -> "~ " ^ (string_of_assertion lass1 escape_string)
	   | LStar (lass1, lass2) -> "(" ^ (string_of_assertion lass1 escape_string) ^ ") * (" ^ (string_of_assertion lass2 escape_string) ^ ")"
	 (*  | LExists (lvl, lass1) -> "exists " ^ (string_of_params lvl) ^ (string_of_assertion lass1 escape_string)
	   | LForAll (lvl, lass1) -> "forall " ^ (string_of_params lvl) ^ (string_of_assertion lass1 escape_string) *) 
	   | LEq (lexpr1, lexpr2) -> (string_of_lexpression lexpr1 escape_string) ^ " == " ^ (string_of_lexpression lexpr2 escape_string)
	   | LLessEq (lexpr1, lexpr2) -> (string_of_lexpression lexpr1 escape_string) ^ " <== " ^ (string_of_lexpression lexpr2 escape_string)
	   | LPointsTo (lexpr1, lexpr2, lexpr3) -> "(" ^ (string_of_lexpression lexpr1 escape_string) ^ ", " ^ (string_of_lexpression lexpr2 escape_string) ^ ") -> " ^ (string_of_lexpression lexpr3 escape_string)
	   | LTrue -> "true"
	   | LFalse -> "false"
	   | LEmp -> "emp")

let rec string_of_cmd sjsil_cmd tabs i line_numbers_on specs_on escape_string =
	let metadata, sjsil_cmd = sjsil_cmd in 
	let str_i = if line_numbers_on then (string_of_int i) ^ " " else "" in
	let str_tabs = tabs_to_str tabs in  
	let ass = metadata.pre_cond in 
	let str_ass = if (specs_on) then (match ass with | None -> "" | Some ass -> str_tabs ^ "[[" ^ string_of_assertion ass escape_string ^ "]]\n") else "" in
	str_ass ^ 
  (match sjsil_cmd with
	(* goto j *) 
  | SGoto j -> 
		let str_j = string_of_int j in 
			str_tabs ^ Printf.sprintf "%sgoto %s" str_i str_j 
  (* goto [e] j k *)
	| SGuardedGoto (e, j, k) -> 
		let str_j = string_of_int j in
		let str_k = string_of_int k in
		let str_e = (string_of_expression e escape_string) in 
			str_tabs ^  Printf.sprintf "%sgoto [%s] %s %s" str_i str_e str_j str_k
	(* basic command *)
	| SBasic bcmd -> str_tabs ^ (string_of_bcmd bcmd i line_numbers_on escape_string)
	(* x := f(y1, ..., yn) with j *)
	| SCall (var, proc_name_expr, arg_expr_list, error_lab) -> 
		let proc_name_expr_str = string_of_expression proc_name_expr escape_string in 
		let error_lab = (match error_lab with | None -> "" | Some error_lab -> ("with " ^ (string_of_int error_lab))) in 
		let se = fun e -> string_of_expression e escape_string in 
		let arg_expr_list_str = match arg_expr_list with
		|	[] -> ""
		| _ -> String.concat ", " (List.map se arg_expr_list) in 
			str_tabs ^  Printf.sprintf "%s%s := %s(%s) %s" str_i var proc_name_expr_str arg_expr_list_str error_lab
	(* var := PHI(var_1, var_2, ..., var_n) *)
	| SPhiAssignment (var, var_arr) -> 
		let len = Array.length var_arr in  
		let rec loop i str_ac =
			if (i >= len) 
				then str_ac 
				else 
					let var_arr_i_str = 
						(match var_arr.(i) with 
						| None -> "$$empty"
						| Some v_i -> v_i) in 
					(if (i == 0)
						then loop 1 var_arr_i_str
						else  loop (i + 1) (str_ac ^ ", " ^ var_arr_i_str)) in 
		let var_arr_str = loop 0 "" in 
		Printf.sprintf "%s%s := PHI(%s)" str_i var var_arr_str
	(* var := PSI(var_1, var_2, ..., var_n) *)
	| SPsiAssignment (var, var_arr) -> 
		let len = Array.length var_arr in  
		let rec loop i str_ac =
			if (i >= len) 
				then str_ac 
				else 
					let var_arr_i_str = 
						(match var_arr.(i) with 
						| None -> "$$empty"
						| Some v_i -> v_i) in 
					(if (i == 0)
						then loop 1 var_arr_i_str
						else  loop (i + 1) (str_ac ^ ", " ^ var_arr_i_str)) in 
		let var_arr_str = loop 0 "" in 
		Printf.sprintf "%s%s := PSI(%s)" str_i var var_arr_str)

let serialize_cmd_arr cmds tabs line_numbers serialize_cmd =
	let number_of_cmds = Array.length cmds in 
	let rec serialize_cmd_arr_iter i str_ac = 
		if (i >= number_of_cmds) 
			then str_ac
			else 
				((let cmd = cmds.(i) in 
				let str_cmd = serialize_cmd cmd tabs i line_numbers in 
				serialize_cmd_arr_iter (i + 1) (str_ac ^ str_cmd ^ "\n"))) in 
	serialize_cmd_arr_iter 0 ""

let sexpr_of_cmd_arr cmds tabs line_numbers =
	serialize_cmd_arr cmds tabs line_numbers sexpr_of_cmd

let string_of_cmd_arr cmds tabs line_numbers =
	let string_of_cmd_aux cmd tabs i line_numbers = 
		string_of_cmd cmd tabs i line_numbers true false in 
	serialize_cmd_arr cmds tabs line_numbers string_of_cmd_aux

(*
  (procedure xpto (arg1 arg2 ...) 
		(body ...) 
		('return ret_var ret_label) 
		('error err_var err_label))
*)
let sexpr_of_procedure proc line_numbers =			
	Printf.sprintf "(procedure \"%s\" \n\t(args%s) \n\t(body \n %s \n\t) \n%s \n %s )" 
  	proc.proc_name 
   	(sexpr_of_params proc.proc_params) 
		(sexpr_of_cmd_arr proc.proc_body 2 line_numbers)
		(match proc.ret_var, proc.ret_label with
		| None, None -> "\t'() \n" 
		| Some var, Some label -> (Printf.sprintf "\t(ret-ctx '%s %s) \n" var (string_of_int label))
		| _, _ -> raise (Failure "Return variable and return label not both present or both absent!"))
		(match proc.error_var, proc.error_label with
		| None, None -> "\t'() \n" 
		| Some var, Some label -> (Printf.sprintf "\t(err-ctx '%s %s) \n" var (string_of_int label))
		| _, _ -> raise (Failure "Error variable and error label not both present or both absent!"))

let rec string_of_outcome o = 
	match o with
	| Normal -> "Normal"
	| Error -> "Error"

let rec string_of_specs (specs : jsil_single_spec list) = 
	match specs with
	| [] -> ""
	| spec :: specs -> 
		"\t[[" ^ string_of_assertion spec.pre false ^ "]]\n" ^ 
		"\t[[" ^ string_of_assertion spec.post false ^ "]]\n" ^ 
		"\t" ^ (match spec.ret_flag with
		| Normal -> "normal"
		| Error -> "error") ^
		(match specs with
		| [] -> ""
		| _ -> "; ") ^ "\n" ^
		string_of_specs specs


(*
  spec xpto (arg1, arg2, ...)
	  [[ ... ]]
		[[ ... ]]
		normal|error;
		...
	proc xpto (arg1, arg2, ...) { 
		cmds
	} with {
		ret: x_ret, i_ret;
		err: x_err, i_err
	}
*)
let string_of_procedure proc line_numbers =			
	(match proc.spec with
	| None -> ""
	| Some spec ->
		Printf.sprintf "spec %s (%s) \n %s \n" spec.spec_name (string_of_params spec.spec_params) (string_of_specs spec.proc_specs)
	)
	^
	(Printf.sprintf "proc %s (%s) { \n %s \n} with {\n%s%s}\n" 
  	proc.proc_name 
   	(string_of_params proc.proc_params) 
		(string_of_cmd_arr proc.proc_body 2 line_numbers)
		(match proc.ret_var, proc.ret_label with
		| None, None -> "" 
		| Some var, Some label -> (Printf.sprintf "\t ret: %s, %s; \n" var (string_of_int label))
		| _, _ -> raise (Failure "Error variable and error label not both present or both absent!"))
		(match proc.error_var, proc.error_label with
		| None, None -> "" 
		| Some var, Some label -> (Printf.sprintf "\t err: %s, %s; \n" var (string_of_int label))
		| _, _ -> raise (Failure "Error variable and error label not both present or both absent!")))


(** Returns a string from a JSIL Logic predicate definition. *)
let string_of_predicate predicate =
	List.fold_left 
		(fun acc_str assertion -> 
			acc_str ^ (Printf.sprintf "pred %s (%s) : %s ;\n"
				predicate.name (string_of_params predicate.params) (string_of_assertion assertion false)))
		""
		predicate.definitions


(**
		Printing out lprocedures

		lproc_body : ((jsil_logic_assertion option * string option * jsil_lab_cmd) array);
*)

let string_of_lcmd lcmd = 
  (match lcmd with
	(* goto j *) 
  | SLGoto j -> 
			Printf.sprintf "goto %s" j 
  (* goto [e] j k *)
	| SLGuardedGoto (e, j, k) -> 
		let str_e = (string_of_expression e false) in 
			Printf.sprintf "goto [%s] %s %s" str_e j k
	(* basic command *)
	| SLBasic bcmd -> (string_of_bcmd bcmd 0 false false)
	(* x := f(y1, ..., yn) with j *)
	| SLCall (var, proc_name_expr, arg_expr_list, error_lab) -> 
		let proc_name_expr_str = string_of_expression proc_name_expr false in 
		let error_lab = (match error_lab with | None -> "" | Some error_lab -> (" with " ^ error_lab)) in 
		let se = fun e -> string_of_expression e false in 
		let arg_expr_list_str = match arg_expr_list with
		|	[] -> ""
		| _ -> String.concat ", " (List.map se arg_expr_list) in 
			Printf.sprintf "%s := %s(%s)%s" var proc_name_expr_str arg_expr_list_str error_lab
	(* var := PHI(var_1, var_2, ..., var_n) *)
	| SLPhiAssignment (var, var_arr) -> 
		let len = Array.length var_arr in  
		let rec loop i str_ac =
			if (i >= len) 
				then str_ac 
				else 
					let var_arr_i_str = 
						(match var_arr.(i) with 
						| None -> "$$empty"
						| Some v_i -> v_i) in 
					(if (i == 0)
						then loop 1 var_arr_i_str
						else  loop (i + 1) (str_ac ^ ", " ^ var_arr_i_str)) in 
		let var_arr_str = loop 0 "" in 
		Printf.sprintf "%s := PHI(%s)" var var_arr_str
	(* var := PSI(var_1, var_2, ..., var_n) *)
	| SLPsiAssignment (var, var_arr) -> 
		let len = Array.length var_arr in  
		let rec loop i str_ac =
			if (i >= len) 
				then str_ac 
				else 
					let var_arr_i_str = 
						(match var_arr.(i) with 
						| None -> "$$empty"
						| Some v_i -> v_i) in 
					(if (i == 0)
						then loop 1 var_arr_i_str
						else  loop (i + 1) (str_ac ^ ", " ^ var_arr_i_str)) in 
		let var_arr_str = loop 0 "" in 
		Printf.sprintf "%s := PSI(%s)" var var_arr_str
	| SLApply (var, arg_expr_list, error_lab) -> 
		let error_lab = (match error_lab with | None -> "" | Some error_lab -> (" with " ^ error_lab)) in 
		let se = fun e -> string_of_expression e false in 
		let arg_expr_list_str = 
			(match arg_expr_list with
		  |	[] -> ""
		  | _ -> String.concat ", " (List.map se arg_expr_list)) in 
			Printf.sprintf "%s := apply (%s)%s" var arg_expr_list_str error_lab
)
		
		
	
let string_of_lbody lbody = 
	let len = Array.length lbody in
	let str = ref "" in
	for i = 0 to (len - 1) do
		let metadata, lab, lcmd = lbody.(i) in
		let spec = metadata.pre_cond in 
		let str_of_spec = 
			(match spec with 
			| None -> "" 
			| Some ass -> "\t\t\t[[" ^ string_of_assertion ass false ^ "]]\n") in
		let str_of_lab  = 
			(match lab with
			| None -> "\t\t\t"
			| Some lab -> "\t" ^ lab ^ ":\t" ^ (if (String.length lab < 7) then "\t" else "")) in
		let str_of_lcmd  = string_of_lcmd lcmd in
		str := !str ^ str_of_spec ^ str_of_lab ^ str_of_lcmd ^
		(if (i = len - 1) then "" else ";") ^ "\n"
	done;
	!str

(** Returns a string from an extended JSIL procedure. *)
let string_of_ext_procedure lproc =
	(match lproc.lspec with
	| None -> ""
	| Some spec ->
		Printf.sprintf "spec %s (%s) \n %s \n" spec.spec_name (string_of_params spec.spec_params) (string_of_specs spec.proc_specs)
	)
	^
	(Printf.sprintf "proc %s (%s) { \n %s \n} with {\n%s%s}" 
  	lproc.lproc_name 
   	(string_of_params lproc.lproc_params) 
		(string_of_lbody lproc.lproc_body)
		(match lproc.lret_var, lproc.lret_label with
		| None, None -> "" 
		| Some var, Some label -> (Printf.sprintf "\t ret: %s, %s; \n" var label)
		| _, _ -> raise (Failure "Error variable and error label not both present or both absent!"))
		(match lproc.lerror_var, lproc.lerror_label with
		| None, None -> "" 
		| Some var, Some label -> (Printf.sprintf "\t err: %s, %s; \n" var label)
		| _, _ -> raise (Failure "Error variable and error label not both present or both absent!")))

let sexpr_of_program program line_numbers = 
	SSyntax.SProgram.fold 
	(fun _ proc acc_str ->
		acc_str ^ "\n" ^ (sexpr_of_procedure proc line_numbers))
	program	
	""

let string_of_program program line_numbers = 
	SSyntax.SProgram.fold 
	(fun _ proc acc_str ->
		acc_str ^ "\n" ^ (string_of_procedure proc line_numbers))
	program	
	""

(** Returns a string from an extended JSIL program. *)
let string_of_ext_program program = 
	let imports_str = 
		(match program.imports with 
		| [] -> ""
		| hd :: tl ->
				"import " ^ (List.fold_left (fun ac import_file -> ac ^ ", " ^ import_file) hd tl) ^ ";\n") in 
	let preds_str =
		Hashtbl.fold
			(fun _ pred acc_str -> acc_str ^ "\n" ^ (string_of_predicate pred)) 
			program.predicates
			"" in
	let procs_str	= 
		Hashtbl.fold 
			(fun _ proc acc_str -> acc_str ^ "\n" ^ (string_of_ext_procedure proc) ^ ";\n") 
			program.procedures
			"" in 
	imports_str ^ preds_str ^ (String.sub procs_str 0 (String.length procs_str - 2))


let serialize_prog_racket prog line_numbers = 
	let serialized_prog	= sexpr_of_program prog line_numbers in 
	Printf.sprintf SSyntax_Templates.template_procs_racket serialized_prog																						

let serialize_internals_racket specs builtins line_numbers = 
	let serialized_specs = sexpr_of_program specs line_numbers in 
	let serialized_builtins = sexpr_of_program builtins line_numbers in 
	let serialized_internals = serialized_specs ^ "\n" ^ serialized_builtins in 
	Printf.sprintf SSyntax_Templates.template_internal_procs_racket serialized_internals

(*
let sexpr_of_heap h = 
	SSyntax.SHeap.fold 
		(fun (loc, prop) hval printed_heap -> 
				let printed_hval = string_of_literal hval false in 
				let printed_cell = Printf.sprintf "\n\t(cell '%s \"%s\" '%s)" loc prop printed_hval in
			printed_heap ^ printed_cell)		
		h
		""
*)

let sexpr_of_heap (h : SSyntax.jsil_lit SSyntax.SHeap.t SSyntax.SHeap.t) = 
	SSyntax.SHeap.fold 
		(fun loc obj printed_heap -> 
			  let printed_object =
					(SSyntax.SHeap.fold
						(fun prop hval print_obj ->
							let printed_hval = string_of_literal hval false in 
							let printed_cell = Printf.sprintf "\n\t(cell '%s \"%s\" '%s)" loc prop printed_hval in
							print_obj ^ printed_cell)
						obj "") in
			printed_heap ^ (printed_object))		
		h
		""
							
(* (define target (heap (cell loc prop val) (cell loc prop val) ... )) *)
let serialize_heap_racket h =  
	let serialized_h = sexpr_of_heap h in 
	Printf.sprintf SSyntax_Templates.template_hp_racket serialized_h

let string_of_store store = 
	Hashtbl.fold 
		(fun (var : string) (v_val : jsil_lit) (ac : string) ->
			let v_val_str = string_of_literal v_val true in 
			let var_val_str = var ^ ": " ^ v_val_str  in 
			if (ac != "") then var_val_str else ac ^ "; " ^ var_val_str)
		store
		"Store: "	
		
		
let string_of_proc_metadata proc = 
	let line_info_lst = 
		List.mapi 
			(fun i (metadata, _) ->
				match metadata.line_offset with 
				| None -> Printf.sprintf "(%d, %d)" i 0
				| Some n ->  Printf.sprintf "(%d, %d)" i n)
			(Array.to_list proc.proc_body) in 
	
	let line_info_str = 
		List.fold_left 
			(fun ac elem -> if (ac = "") then elem else ac ^ "\n" ^ elem)
			""
			line_info_lst in 
	"Proc: " ^ proc.proc_name ^ "\n" ^ line_info_str  
	

let string_of_ext_proc_metadata ext_proc = 
	let line_info_lst = 
		List.mapi 
			(fun i (metadata, label, cmd) ->
				match metadata.line_offset with 
				| None -> Printf.sprintf "(%d, %d)" i 0
				| Some n ->  Printf.sprintf "(%d, %d)" i n) 
			(Array.to_list ext_proc.lproc_body) in 
	
	let line_info_str = 
		List.fold_left 
			(fun ac elem -> if (ac = "") then elem else ac ^ "\n" ^ elem)
			""
			line_info_lst in 
	"Proc: " ^ ext_proc.lproc_name ^ "\n" ^ line_info_str


let string_of_ext_prog_metadata ext_prog =
	Hashtbl.fold
		(fun _ ext_proc acc_str ->
			if (acc_str = "")
				then (string_of_ext_proc_metadata ext_proc)
				else acc_str ^ "\n" ^ (string_of_ext_proc_metadata ext_proc))
		ext_prog
		""

let string_of_prog_metadata prog = 
	SSyntax.SProgram.fold 
		(fun _ proc acc_str -> 
			if (acc_str = "") 
				then (string_of_proc_metadata proc)
				else acc_str ^ "\n" ^ (string_of_proc_metadata proc)) 
		prog	
		""  		
	
	