open JSIL_Syntax

let rec tabs_to_str i  = 
	if i = 0 then "" else "\t" ^ (tabs_to_str (i - 1))

(***
 Generate strings from JSIL program types
*)

let string_of_float x = 
	if (x == nan) 
		then "nan"
		else if (x == neg_infinity) 
			then "-inf"
			else if (x == infinity) 
				then "inf"
				else string_of_float x

(** JSIL types *)
let string_of_type t =
  match t with
  | UndefinedType -> "$$undefined_type"
	| NullType -> "$$null_type"
	| EmptyType -> "$$empty_type"
	| NoneType -> "$$none_type"
  | BooleanType -> "$$boolean_type"
	| IntType -> "$$int_type"
  | NumberType -> "$$number_type"
	| StringType -> "$$string_type"
  | ObjectType -> "$$object_type"
  | ReferenceType -> "$$reference_type"
	| ObjectReferenceType -> "$$o-reference_type"
	| VariableReferenceType -> "$$v-reference_type"	
	| ListType -> "$$list_type"
	| TypeType -> "$$type_type"

(** JSIL constants *)
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

(** JSIL literals *)
let rec string_of_literal lit escape_string =
	let sl = fun l -> string_of_literal l escape_string in
  match lit with
	| Undefined -> "$$undefined"
	| Null -> "$$null"
	| Empty -> "$$empty"
	| Constant c -> string_of_constant c
	| Bool b ->
		(match b with
    | true -> "$$t"
    | false -> "$$f")
	| Integer i -> string_of_int i
  | Num n -> string_of_float n
  | String x ->
		(if escape_string
			then Printf.sprintf "\\\"%s\\\"" x
			else Printf.sprintf "\"%s\"" x)
  | Loc loc -> loc
  | Type t -> string_of_type t
	| LVRef (l, x) -> Printf.sprintf "%s.v.%s" (sl l) x
	| LORef (l, x) -> Printf.sprintf "%s.o.%s" (sl l) x
	| LList ll ->
		(match ll with
		| [] -> "$$nil"
		| ll -> Printf.sprintf "{{ %s }}" (String.concat ", " (List.map sl ll)))

(** JSIL binary operators *)
let string_of_binop bop =
	match bop with
  | Equal -> "="
  | LessThan -> "<"
	| LessThanEqual -> "<="
	| LessThanString -> "<s"
 	| Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Div -> "/"
  | Mod -> "%"
	| And -> "and"
  | Or -> "or"
	| BitwiseAnd -> "&"
  | BitwiseOr -> "|"
  | BitwiseXor -> "^"
	| LeftShift -> "<<"
  | SignedRightShift -> ">>"
  | UnsignedRightShift -> ">>>"
	| M_atan2 -> "m_atan2"
	| M_pow -> "**"
	| Subtype -> "<:"
	| LstCons -> "::"
	| LstCat -> "@"
	| StrCat -> "++"

(** JSIL unary operators *)
let string_of_unop uop =
	match uop with
  | UnaryMinus -> "-"
  | Not -> "not"
	| BitwiseNot -> "~"
	| M_abs -> "m_abs"
	| M_acos -> "m_acos"
	| M_asin -> "m_asin"
	| M_atan -> "m_atan"
	| M_ceil -> "m_ceil"
	| M_cos -> "m_cos"
	| M_exp -> "m_exp"
	| M_floor -> "m_floor"
	| M_log -> "m_log"
	| M_round -> "m_round"
	| M_sgn -> "m_sgn"
	| M_sin -> "m_sin"
	| M_sqrt -> "m_sqrt"
	| M_tan -> "m_tan"
	| IsPrimitive -> "is_primitive"
  | ToStringOp -> "num_to_string"
	| ToIntOp -> "num_to_int"
	| ToUint16Op -> "num_to_uint16"
  | ToInt32Op -> "num_to_int32"
  | ToUint32Op -> "num_to_uint32"
	| ToNumberOp -> "string_to_num"
	| Car -> "car"
	| Cdr -> "cdr"
	| LstLen -> "l-len"
	| StrLen -> "s-len"

(** JSIL expressions *)
let rec string_of_expression e escape_string =
  let se = fun e -> string_of_expression e escape_string in
  match e with
    | Literal l -> string_of_literal l escape_string
    | Var v -> v
		(* (e1 bop e2) *)
    | BinOp (e1, op, e2) -> Printf.sprintf "(%s %s %s)" (se e1) (string_of_binop op) (se e2)
		(* (uop e) *)
    | UnaryOp (op, e) -> Printf.sprintf "(%s %s)" (string_of_unop op) (se e)
		(* v-ref(e1 e2) *)
    | VRef (e1, e2) -> Printf.sprintf "v-ref(%s, %s)" (se e1) (se e2)
  	(* o-ref(e1 e2) *)
    | ORef (e1, e2) -> Printf.sprintf "o-ref(%s, %s)" (se e1) (se e2)
		(* base(e) *)
    | Base e -> Printf.sprintf "base(%s)" (se e)
		(* field(e) *)
    | Field e -> Printf.sprintf "field(%s)" (se e)
		(* typeof(e) *)
    | TypeOf e -> Printf.sprintf "typeOf(%s)" (se e)
		(* assume(e) *) 
		| RAssume e -> Printf.sprintf "assume(%s)" (se e)
		(* assert(e) *)
		| RAssert e -> Printf.sprintf "assert(%s)" (se e)
		(* make-symbol-number() *) 
		| RNumSymb -> "make-symbol-number()" 
		(* make-symbol-string() *) 
		| RStrSymb -> "make-symbol-string()"
		(* {{ e1, e2, ... }} *)
		| EList ll -> 
			(match ll with
			| [] -> "$$nil"
			| ll -> Printf.sprintf "{{ %s }}" (String.concat ", " (List.map se ll)))
		(* l-nth(e1, e2) *)
		| LstNth (e1, e2) -> Printf.sprintf "l-nth(%s, %s)" (se e1) (se e2)
		(* s-nth(e1, e2) *)
		| StrNth (e1, e2) -> Printf.sprintf "s-nth(%s, %s)" (se e1) (se e2)

(** JSIL Basic statements *)
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

(** JSIL logical expressions *)
let rec string_of_logic_expression e escape_string =
  let sle = fun e -> string_of_logic_expression e escape_string in
  match e with
    | LLit llit -> string_of_literal llit escape_string
		| LNone -> "None"
    | LVar lvar -> Printf.sprintf "(Lvar %s)" lvar
		| ALoc aloc -> Printf.sprintf "(Aloc %s)" aloc
		| PVar pvar -> Printf.sprintf "(Pvar %s)" pvar
		(* (e1 bop e2) *)
    | LBinOp (e1, op, e2) -> Printf.sprintf "(%s %s %s)" (sle e1) (string_of_binop op) (sle e2)
		(* (uop e1 e2) *)
    | LUnOp (op, e) -> Printf.sprintf "(%s %s)" (string_of_unop op) (sle e)
		(* v-ref(e1, e2) *)
    | LEVRef (e1, e2) -> Printf.sprintf "v-ref(%s, %s)" (sle e1) (sle e2)
  	(* o-ref(e1, e2) *)
    | LEORef (e1, e2) -> Printf.sprintf "o-ref(%s, %s)" (sle e1) (sle e2)
		(* base(e) *)
    | LBase e -> Printf.sprintf "base(%s)" (sle e)
		(* field(e) *)
    | LField e -> Printf.sprintf "field(%s)" (sle e)
		(* typeOf(e) *)
    | LTypeOf e -> Printf.sprintf "typeOf(%s)" (sle e)
		(* {{ e1, ..., en }} *)
    | LEList list ->
			(match list with
			| [] -> "$$nil"
			| ll -> Printf.sprintf "{{ %s }}" (String.concat ", " (List.map sle ll)))
		(* l-nth(e1, e2) *)
		| LLstNth (e1, e2) -> Printf.sprintf "l-nth(%s, %s)" (sle e1) (sle e2)
		(* s-nth(e1, e2) *)
		| LStrNth (e1, e2) -> Printf.sprintf "s-nth(%s, %s)" (sle e1) (sle e2)
		(* $$unknown *)
		| LUnknown -> "$$unknown"

(** JSIL logic assertions *)
let rec string_of_logic_assertion a escape_string =
	let sla = fun a -> string_of_logic_assertion a escape_string in
	let sle = fun e -> string_of_logic_expression e escape_string in
	match a with
		(* a1 /\ a2 *)
		| LAnd (a1, a2) -> Printf.sprintf "%s /\\ %s" (sla a1) (sla a2)
		(* a1 \/ a2 *)
		| LOr (a1, a2) -> Printf.sprintf "%s \\/ %s" (sla a1) (sla a2)
		(* ! a *)
		| LNot a -> Printf.sprintf "! %s" (sla a)
		(* true *)
		| LTrue -> "true"
		(* false *)
		| LFalse -> "false"
		(* e1 == e2 *)
		| LEq (e1, e2) -> Printf.sprintf "%s == %s" (sle e1) (sle e2)
		(* e1 << e2 *)
		| LLess (e1, e2) -> Printf.sprintf "%s <# %s" (sle e1) (sle e2)
		(* e1 <<= e2 *)
		| LLessEq (e1, e2) -> Printf.sprintf "%s <=# %s" (sle e1) (sle e2)
		(* e1 <<s e2 *)
		| LStrLess (e1, e2) -> Printf.sprintf "%s <s# %s" (sle e1) (sle e2)
		(* a1 * a2 *)
		| LStar (a1, a2) -> Printf.sprintf "%s * %s" (sla a1) (sla a2)
		(* (e1, e2) -> e3 *)
		| LPointsTo (e1, e2, e3) -> Printf.sprintf "(%s, %s) -> %s" (sle e1) (sle e2) (sle e3)
		(* emp *)
		| LEmp -> "emp"
		(* exists vars . a 
		| LExists (lvars, a) -> Printf.sprintf "exists %s . %s" (String.concat ", " lvars) (sla a) *)
		(* forall vars . a 
		| LForAll (lvars, a) -> Printf.sprintf "forall %s . %s" (String.concat ", " lvars) (sla a) *)
		(* x(y1, ..., yn) *)
		| LPred (name, params) -> Printf.sprintf "%s(%s)" name (String.concat ", " (List.map sle params))
		(* types(e1:t1, ..., en:tn) *)
		| LTypes type_list -> Printf.sprintf "types(%s)"
			(String.concat ", " (List.map (fun (e, t) -> Printf.sprintf "%s : %s" (sle e) (string_of_type t)) type_list))

(** JSIL logic predicates *)
let rec string_of_predicate predicate =
	let sle = fun e -> string_of_logic_expression e false in
	List.fold_left 
		(fun acc_str assertion -> 
			acc_str ^ (Printf.sprintf "pred %s (%s) : %s;\n"
				predicate.name
				(String.concat ", " (List.map sle predicate.params))
				(string_of_logic_assertion assertion false)))
		""
		predicate.definitions

(** JSIL All Statements *)
let rec string_of_cmd sjsil_cmd tabs i line_numbers_on specs_on escape_string =
	let se = fun e -> string_of_expression e escape_string in
	let str_i = if line_numbers_on then (string_of_int i) ^ ". " else "" in
	let str_tabs = tabs_to_str tabs in
	
	let metadata, sjsil_cmd = sjsil_cmd in
	let ass = metadata.pre_cond in
	let str_ass =
		if (specs_on)
		then
		  (match ass with
		  | None -> ""
		  | Some ass -> str_tabs ^ "[[" ^ string_of_logic_assertion ass escape_string ^ "]]\n")
		else "" in
	str_ass ^ 
  (match sjsil_cmd with
	(* Basic command *)
	| SBasic bcmd ->
		str_tabs ^ (string_of_bcmd bcmd i line_numbers_on escape_string)
	(* goto j *)
  | SGoto j ->
		str_tabs ^ Printf.sprintf "%sgoto %s" str_i (string_of_int j)
  (* goto [e] j k *)
	| SGuardedGoto (e, j, k) ->
		str_tabs ^ Printf.sprintf "%sgoto [%s] %s %s" str_i (se e) (string_of_int j) (string_of_int k)
	(* x := f(y1, ..., yn) with j *)
	| SCall (var, name, args, error) ->
		str_tabs ^  Printf.sprintf "%s%s := %s(%s) %s" str_i var (se name) (String.concat ", " (List.map se args))
			(match error with
			| None -> ""
			| Some index -> ("with " ^ (string_of_int index)))
	(* x := apply(y1, ..., yn) with j *)
	| SApply (var, args, error) ->
		Printf.sprintf "%s := apply(%s)%s" var (String.concat ", " (List.map se args))
		  (match error with
			| None -> ""
			| Some index -> (" with " ^ (string_of_int index)))
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

let string_of_cmd_arr cmds tabs line_numbers =
	let string_of_cmd_aux cmd tabs i line_numbers = 
		string_of_cmd cmd tabs i line_numbers true false in 
	serialize_cmd_arr cmds tabs line_numbers string_of_cmd_aux

(** JSIL spec return flag *)
let string_of_return_flag flag =
	match flag with
		| Normal -> "normal"
		| Error -> "error"

(** JSIL procedure specification *)
let rec string_of_specs specs =
	match specs with
	| [] -> ""
	| hd :: tl ->
		"\t[[" ^ string_of_logic_assertion hd.pre false ^ "]]\n" ^
		"\t[[" ^ string_of_logic_assertion hd.post false ^ "]]\n" ^
		"\t" ^ string_of_return_flag hd.ret_flag ^
		(match tl with
		| [] -> "\n"
		| _ -> ";\n" ^ string_of_specs tl)

(** JSIL procedures *)
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
	(* Optional specification block *)
	(match proc.spec with
	| None -> ""
	| Some spec ->
		Printf.sprintf "spec %s (%s)\n %s\n" spec.spec_name (String.concat ", " spec.spec_params)
		  (string_of_specs spec.proc_specs))
	^
	(* Procedure definition block *)
	(Printf.sprintf "proc %s (%s) {\n%s} with {\n%s%s};\n"
  	proc.proc_name 
   	(String.concat ", " proc.proc_params) 
		(string_of_cmd_arr proc.proc_body 2 line_numbers)
		(match proc.ret_var, proc.ret_label with
		| None, None -> "" 
		| Some var, Some label -> (Printf.sprintf "\tret: %s, %s;\n" var (string_of_int label))
		| _, _ -> raise (Failure "Error: variable and error label not both present or both absent!"))
		(match proc.error_var, proc.error_label with
		| None, None -> "" 
		| Some var, Some label -> (Printf.sprintf "\terr: %s, %s;\n" var (string_of_int label))
		| _, _ -> raise (Failure "Error: variable and error label not both present or both absent!")))

(** JSIL programs *)
let string_of_program program line_numbers = 
	Hashtbl.fold 
		(fun _ proc acc_str -> acc_str ^ "\n" ^ (string_of_procedure proc line_numbers))
		program
		""


(** JSIL procedures with labels *)
let string_of_lab_cmd lcmd =
	let se = fun e -> string_of_expression e false in
  match lcmd with
	(* Basic command *)
	| SLBasic bcmd ->
		(string_of_bcmd bcmd 0 false false)
	(* goto j *) 
  | SLGoto j ->
		Printf.sprintf "goto %s" j
  (* goto [e] j k *)
	| SLGuardedGoto (e, j, k) ->
		Printf.sprintf "goto [%s] %s %s" (se e) j k
	(* x := f(y1, ..., yn) with j *)
	| SLCall (var, name, args, error) ->
		Printf.sprintf "%s := %s(%s)%s" var (se name) (String.concat ", " (List.map se args))
		  (match error with
			| None -> ""
			| Some label -> (" with " ^ label))
	(* x := apply(y1, ..., yn) with j *)
	| SLApply (var, args, error) ->
		Printf.sprintf "%s := apply(%s)%s" var (String.concat ", " (List.map se args))
		  (match error with
			| None -> ""
			| Some label -> (" with " ^ label))
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

let string_of_lbody lbody = 
	let len = Array.length lbody in
	let str = ref "" in
	for i = 0 to (len - 1) do
		let metadata, lab, lcmd = lbody.(i) in
		let spec = metadata.pre_cond in 
		let str_of_spec = 
			(match spec with 
			| None -> "" 
			| Some ass -> "\t\t\t[[" ^ string_of_logic_assertion ass false ^ "]]\n") in
		let str_of_lab  = 
			(match lab with
			| None -> "\t\t\t"
			| Some lab -> "\t" ^ lab ^ ":\t" ^ (if (String.length lab < 7) then "\t" else "")) in
		let str_of_lcmd  = string_of_lab_cmd lcmd in
		str := !str ^ str_of_spec ^ str_of_lab ^ str_of_lcmd ^
		(if (i = len - 1) then "" else ";") ^ "\n"
	done;
	!str

(** Extended JSIL procedures *)
let string_of_ext_procedure proc =
	(* Optional specification block *)
	(match proc.lspec with
	| None -> ""
	| Some spec ->
		Printf.sprintf "spec %s (%s)\n %s\n" spec.spec_name (String.concat ", " spec.spec_params)
		  (string_of_specs spec.proc_specs))
	^
	(* Procedure definition block *)
	(Printf.sprintf "proc %s (%s) {\n%s} with {\n%s%s};\n"
  	proc.lproc_name 
   	(String.concat ", " proc.lproc_params) 
		(string_of_lbody proc.lproc_body)
		(match proc.lret_var, proc.lret_label with
		| None, None -> "" 
		| Some var, Some label -> (Printf.sprintf "\tret: %s, %s;\n" var label)
		| _, _ -> raise (Failure "Error: variable and error label not both present or both absent!"))
		(match proc.lerror_var, proc.lerror_label with
		| None, None -> "" 
		| Some var, Some label -> (Printf.sprintf "\terr: %s, %s;\n" var label)
		| _, _ -> raise (Failure "Error: variable and error label not both present or both absent!")))

(** Extended JSIL programs *)
let string_of_ext_program program =
	(* Imports line *)
	(match program.imports with
	| [] -> ""
	| hd :: tl -> "import " ^ (String.concat ", " (hd :: tl)) ^ ";\n")
	^
	(* Predicates *)
	(Hashtbl.fold
		(fun _ pred acc_str -> acc_str ^ "\n" ^ (string_of_predicate pred))
		program.predicates
		"")
	^
	(* Procedures *)
	Hashtbl.fold
		(fun _ proc acc_str -> acc_str ^ "\n" ^ (string_of_ext_procedure proc))
		program.procedures
		""


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

let string_of_prog_metadata prog = 
	Hashtbl.fold 
		(fun _ proc acc_str -> 
			if (acc_str = "") 
				then (string_of_proc_metadata proc)
				else acc_str ^ "\n" ^ (string_of_proc_metadata proc)) 
		prog	
		""

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

let str_of_assertion_list a_list = 
	List.fold_left 
		(fun ac a -> 
			let a_str = string_of_logic_assertion a false in 
			if (ac = "") then a_str else (ac ^ ", " ^ a_str))
			""
			a_list 