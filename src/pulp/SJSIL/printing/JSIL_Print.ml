open SJSIL_Constants
open SJSIL_Syntax

let fresh_sth (name : string) : (unit -> string) =
  let counter = ref 0 in
  let rec f () =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f

let fresh_symbol : (unit -> string) = fresh_sth "symb_"

let rec tabs_to_str i  = 
	if i == 0 then "" else "\t" ^ (tabs_to_str (i - 1))

(***
 Generate strings from JSIL programs
*)

let string_of_float x = 
	if (x == nan) 
		then "+nan.0"
		else if (x == neg_infinity) 
			then "-inf.0"
			else if (x == infinity) 
				then "+inf.0"
				else string_of_float x 

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

let string_of_type t =
  match t with
  | NullType -> "$$null_type"
  | UndefinedType -> "$$undefined_type"
  | BooleanType -> "$$boolean_type"
  | StringType -> "$$string_type"
  | NumberType -> "$$number_type"
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

let string_of_list list =
	match list with
	| [] -> ""
	| elem :: rest ->
  	List.fold_left 
  		(fun prev_elems elem -> prev_elems ^ ", " ^ elem) elem rest

(** Returns a string from a JSIL Logic expression. *)
let rec string_of_logic_expression e escape_string =
  let sle = fun e -> string_of_logic_expression e escape_string in
  match e with
    | LLit llit -> string_of_literal llit escape_string
		| LNone -> "none"
    | LVar lvar -> lvar
		| ALoc aloc -> aloc
		| PVar pvar -> pvar
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
		(* typeof(e) *)
    | LTypeOf e -> Printf.sprintf "typeof(%s)" (sle e)
		(* (cons(e) *)
		| LCons (e1, e2) -> Printf.sprintf "cons(%s, %s)" (sle e1) (sle e2) 
		(* {{  }}*) 
    | LEList list -> 
			(match list with
			| [] -> "$$nil"
			| ll ->
			let rec loop ll = 
				(match ll with
				| [] -> ""
				| e :: ll -> 
					let scar = sle e in
					let ssep = 
						(match ll with
						| [] -> ""
						| _ -> ", ") in
					let scdr = loop ll in
					Printf.sprintf ("%s%s%s") scar ssep scdr)
			in Printf.sprintf "{{ %s }}" (loop ll))
		(* s-nth(e, n) *)
		| LSNth (e1, e2) -> Printf.sprintf "s-nth(%s, %s)" (sle e1) (sle e2)
		(* (l-nth(e, n) *)
		| LLNth (e1, e2) -> Printf.sprintf "l-nth(%s, %s)" (sle e1) (sle e2)
		(* $$unknown *) 
		| LUnknown -> "$$unknown"

(** Returns a string from a JSIL Logic predicate definition. *)
let rec string_of_predicate predicate =
	List.fold_left 
		(fun acc_str assertion -> 
			acc_str ^ (Printf.sprintf "pred %s (%s) : %s ;\n"
				predicate.name (string_of_list predicate.params) (string_of_logic_assertion assertion false)))
		""
		predicate.definitions
and
(** Returns a string from a JSIL Logic assertion. *)
string_of_logic_assertion a escape_string =
	let sla = fun a -> string_of_logic_assertion a escape_string in
	let sle = fun e -> string_of_logic_expression e escape_string in
	match a with
		(* a1 /\ a2 *)
		| LAnd (a1, a2) -> Printf.sprintf "%s /\\ %s" (sla a1) (sla a2)
		(* a1 \/ a2 *)
		| LOr (a1, a2) -> Printf.sprintf "%s \\/ %s" (sla a1) (sla a2)
		(* ~ a *)
		| LNot a -> Printf.sprintf "~ %s" (sla a)
		(* true *)
		| LTrue -> Printf.sprintf "true"
		(* false *)
		| LFalse -> Printf.sprintf "false"
		(* e1 == e2 *)
		| LEq (e1, e2) -> Printf.sprintf "%s == %s" (sle e1) (sle e2)
		(* e1 <== e2 *)
		| LLessEq (e1, e2) -> Printf.sprintf "%s <== %s" (sle e1) (sle e2)
		(* a1 * a2 *)
		| LStar (a1, a2) -> Printf.sprintf "%s * %s" (sla a1) (sla a2)
		(* (e1, e2) -> e3 *)
		| LPointsTo (e1, e2, e3) -> Printf.sprintf "(%s, %s) -> %s" (sle e1) (sle e2) (sle e3)
		(* emp *)
		| LEmp -> Printf.sprintf "emp"
		(* exists vars . a *)
		| LExists (lvars, a) -> Printf.sprintf "exists %s . %s" (string_of_list lvars) (sla a)
		(* forall vars . a *)
		| LForAll (lvars, a) -> Printf.sprintf "forall %s . %s" (string_of_list lvars) (sla a)

(** Returns a string from a JSIL command. *)
let rec string_of_cmd sjsil_cmd tabs i line_numbers_on specs_on escape_string =
	let metadata, sjsil_cmd = sjsil_cmd in 
	let str_i = if line_numbers_on then (string_of_int i) ^ " " else "" in
	let str_tabs = tabs_to_str tabs in  
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

let string_of_cmd_arr cmds tabs line_numbers =
	let string_of_cmd_aux cmd tabs i line_numbers = 
		string_of_cmd cmd tabs i line_numbers true false in 
	serialize_cmd_arr cmds tabs line_numbers string_of_cmd_aux

let string_of_return_flag flag =
	match flag with
		| Normal -> "normal"
		| Error -> "error"

(** Returns a string from a JSIL procedure specification. *)
let rec string_of_specs (specs : jsil_single_spec list) = 
	match specs with
	| [] -> ""
	| spec :: specs -> 
		"\t[[" ^ string_of_logic_assertion spec.pre false ^ "]]\n" ^ 
		"\t[[" ^ string_of_logic_assertion spec.post false ^ "]]\n" ^ 
		"\t" ^ string_of_return_flag spec.ret_flag ^
		(match specs with
		| [] -> ""
		| _ -> "; ") ^ "\n" ^
		string_of_specs specs

(** Returns a string from a JSIL procedure. *)
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
		Printf.sprintf "spec %s (%s) \n %s \n" spec.spec_name (string_of_list spec.spec_params) (string_of_specs spec.proc_specs)
	)
	^
	(Printf.sprintf "proc %s (%s) { \n %s \n} with {\n%s%s}\n" 
  	proc.proc_name 
   	(string_of_list proc.proc_params) 
		(string_of_cmd_arr proc.proc_body 2 line_numbers)
		(match proc.ret_var, proc.ret_label with
		| None, None -> "" 
		| Some var, Some label -> (Printf.sprintf "\t ret: %s, %s; \n" var (string_of_int label))
		| _, _ -> raise (Failure "Error variable and error label not both present or both absent!"))
		(match proc.error_var, proc.error_label with
		| None, None -> "" 
		| Some var, Some label -> (Printf.sprintf "\t err: %s, %s; \n" var (string_of_int label))
		| _, _ -> raise (Failure "Error variable and error label not both present or both absent!")))

(** Returns a string from a JSIL program. *)
let string_of_program program line_numbers = 
	Hashtbl.fold 
	(fun _ proc acc_str ->
		acc_str ^ "\n" ^ (string_of_procedure proc line_numbers))
	program	
	""

(**
		Printing out lprocedures

		lproc_body : ((jsil_logic_assertion option * string option * jsil_lab_cmd) array);
*)

let string_of_lab_cmd lcmd = 
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

(** Returns a string from an extended JSIL procedure. *)
let string_of_ext_procedure lproc =
	(match lproc.lspec with
	| None -> ""
	| Some spec ->
		Printf.sprintf "spec %s (%s) \n %s \n" spec.spec_name (string_of_list spec.spec_params) (string_of_specs spec.proc_specs)
	)
	^
	(Printf.sprintf "proc %s (%s) { \n %s \n} with {\n%s%s}" 
  	lproc.lproc_name 
   	(string_of_list lproc.lproc_params) 
		(string_of_lbody lproc.lproc_body)
		(match lproc.lret_var, lproc.lret_label with
		| None, None -> "" 
		| Some var, Some label -> (Printf.sprintf "\t ret: %s, %s; \n" var label)
		| _, _ -> raise (Failure "Error variable and error label not both present or both absent!"))
		(match lproc.lerror_var, lproc.lerror_label with
		| None, None -> "" 
		| Some var, Some label -> (Printf.sprintf "\t err: %s, %s; \n" var label)
		| _, _ -> raise (Failure "Error variable and error label not both present or both absent!")))

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


let string_of_store store = 
	Hashtbl.fold 
		(fun (var : string) (v_val : jsil_lit) (ac : string) ->
			let v_val_str = string_of_literal v_val true in 
			let var_val_str = var ^ ": " ^ v_val_str  in 
			if (ac != "") then var_val_str else ac ^ "; " ^ var_val_str)
		store
		"Store: "
