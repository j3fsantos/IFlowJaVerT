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
	| NullType      -> "$$null_type"
	| EmptyType     -> "$$empty_type"
	| NoneType      -> "$$none_type"
  	| BooleanType   -> "$$boolean_type"
  	| NumberType    -> "$$number_type"
	| StringType    -> "$$string_type"
	| CharType      -> "$$char_type"
  	| ObjectType    -> "$$object_type"
	| ListType      -> "$$list_type"
	| TypeType      -> "$$type_type"
	| SetType       -> "$$set_type"


(** JSIL constants *)
let string_of_constant c =
	match c with
	| Min_float -> "$$min_value"
	| Max_float -> "$$max_value"
	| Random    -> "$$random"
	| E         -> "$$e"
	| Ln10      -> "$$ln10"
	| Ln2       -> "$$ln2"
	| Log2e     -> "$$log2e"
	| Log10e    -> "$$log10e"
	| Pi        -> "$$pi"
	| Sqrt1_2   -> "$$sqrt1_2"
	| Sqrt2     -> "$$sqrt2"
	| UTCTime   -> "$$utctime"
	| LocalTime -> "$$localtime"


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
  	| Num n -> string_of_float n
  	| String x ->
		(if escape_string
			then Printf.sprintf "\\\"%s\\\"" x
			else Printf.sprintf "\"%s\"" x)
	| Char x ->
		(if escape_string
			then Printf.sprintf "\\\'%c\\\'" x
			else Printf.sprintf "\'%c\'" x)
	| Loc loc -> loc
  	| Type t -> string_of_type t
	| LList ll ->
		(match ll with
		| [] -> "$$nil"
		| ll -> Printf.sprintf "{{ %s }}" (String.concat ", " (List.map sl ll)))
	| CList cl ->
		(match cl with
		| [] -> "''"
		| cl -> Printf.sprintf "[[%s]]" (String.concat ", " (List.map sl cl)))


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
	| LstCons -> "::"
	| LstCat -> "@"
	| StrCat -> "++"
	| CharCons -> ":c:"
	| CharCat -> "+c+"
	| SetDiff -> "-d-"
	| SetMem -> "-e-"
	| SetSub -> "-s-"

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
    | UnOp (op, e) -> Printf.sprintf "(%s %s)" (string_of_unop op) (se e)
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
		(* -{ e1, e2, ... }- *)
		| ESet ll -> Printf.sprintf "-{ %s }-" (String.concat ", " (List.map se ll))
		(* [['c1', 'c2',...]]*)
		| CList ll ->
			(match ll with
			| [] -> "''"
			| ll -> Printf.sprintf "[[%s]]" (String.concat ", " (List.map se ll)))
		(* l-nth(e1, e2) *)
		| LstNth (e1, e2) -> Printf.sprintf "l-nth(%s, %s)" (se e1) (se e2)
		(* s-nth(e1, e2) *)
		| StrNth (e1, e2) -> Printf.sprintf "s-nth(%s, %s)" (se e1) (se e2)
		| SetUnion le -> Printf.sprintf "-u- (%s)" (String.concat ", " (List.map se le))
		| SetInter le -> Printf.sprintf "-i- (%s)" (String.concat ", " (List.map se le))

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
	(* x := deleteObj(e1) *)
	| SDeleteObj (e1) ->  Printf.sprintf "%sdeleteObject (%s)" str_i (se e1)
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
    | LVar lvar -> lvar (* Printf.sprintf "(Lvar %s)" lvar *)
	| ALoc aloc -> aloc (* Printf.sprintf "(Aloc %s)" aloc *)
	| PVar pvar -> pvar (* Printf.sprintf "(Pvar %s)" pvar *)
	(* (e1 bop e2) *)
    | LBinOp (e1, op, e2) -> Printf.sprintf "(%s %s %s)" (sle e1) (string_of_binop op) (sle e2)
	(* (uop e1 e2) *)
    | LUnOp (op, e) -> Printf.sprintf "(%s %s)" (string_of_unop op) (sle e)
	(* typeOf(e) *)
    | LTypeOf e -> Printf.sprintf "typeOf(%s)" (sle e)
	(* {{ e1, ..., en }} *)
    | LEList list ->
			(match list with
			| [] -> "$$nil"
			| ll -> Printf.sprintf "{{ %s }}" (String.concat ", " (List.map sle ll)))
		(* -{ e1, ..., en }- *)
    | LESet list -> Printf.sprintf "-{ %s }-" (String.concat ", " (List.map sle list))
    | LSetUnion list -> Printf.sprintf "-u- (%s)" (String.concat ", " (List.map sle list))
    | LSetInter list -> Printf.sprintf "-i- (%s)" (String.concat ", " (List.map sle list))
	| LCList list ->
			(match list with
			| [] -> "''"
			| ll -> Printf.sprintf "[[%s]]" (String.concat ", " (List.map sle ll)))
		(* l-nth(e1, e2) *)
	| LLstNth (e1, e2) -> Printf.sprintf "l-nth(%s, %s)" (sle e1) (sle e2)
	(* s-nth(e1, e2) *)
	| LStrNth (e1, e2) -> Printf.sprintf "s-nth(%s, %s)" (sle e1) (sle e2)

(** JSIL logic assertions *)
let rec string_of_logic_assertion a escape_string =
	let sla = fun a -> string_of_logic_assertion a escape_string in
	let sle = fun e -> string_of_logic_expression e escape_string in
	match a with
		(* a1 /\ a2 *)
		| LAnd (a1, a2) -> Printf.sprintf "(%s /\\ %s)" (sla a1) (sla a2)
		(* a1 \/ a2 *)
		| LOr (a1, a2) -> Printf.sprintf "(%s \\/ %s)" (sla a1) (sla a2)
		(* ! a *)
		| LNot a -> Printf.sprintf "(! %s)" (sla a)
		(* true *)
		| LTrue -> "true"
		(* false *)
		| LFalse -> "false"
		(* e1 == e2 *)
		| LEq (e1, e2) -> Printf.sprintf "(%s == %s)" (sle e1) (sle e2)
		(* e1 << e2 *)
		| LLess (e1, e2) -> Printf.sprintf "(%s <# %s)" (sle e1) (sle e2)
		(* e1 <<= e2 *)
		| LLessEq (e1, e2) -> Printf.sprintf "(%s <=# %s)" (sle e1) (sle e2)
		(* e1 <<s e2 *)
		| LStrLess (e1, e2) -> Printf.sprintf "(%s <s# %s)" (sle e1) (sle e2)
		(* a1 * a2 *)
		| LStar (a1, a2) -> Printf.sprintf "%s * %s" (sla a1) (sla a2)
		(* (e1, e2) -> e3 *)
		| LPointsTo (e1, e2, e3) -> Printf.sprintf "((%s, %s) -> %s)" (sle e1) (sle e2) (sle e3)
		(* emp *)
		| LEmp -> "emp"
		(* exists vars . a
		| LExists (lvars, a) -> Printf.sprintf "exists %s . %s" (String.concat ", " lvars) (sla a) *)
		(* forall vars . a *)
		| LForAll (lvars, a) -> Printf.sprintf "(forall %s . %s)" (String.concat ", "
				(List.map (fun (x, t) -> Printf.sprintf "%s : %s" x (string_of_type t)) lvars)) (sla a)
		(* x(y1, ..., yn) *)
		| LPred (name, params) -> Printf.sprintf "%s(%s)" name (String.concat ", " (List.map sle params))
		(* types(e1:t1, ..., en:tn) *)
		| LTypes type_list -> Printf.sprintf "types(%s)"
			(String.concat ", " (List.map (fun (e, t) -> Printf.sprintf "%s : %s" (sle e) (string_of_type t)) type_list))
		| LEmptyFields (obj, domain) ->
			Printf.sprintf "empty_fields(%s : %s)" (sle obj) (sle domain)
		(* e1 --e-- e2 *)
		| LSetMem (e1, e2) -> Printf.sprintf "(%s --e-- %s)" (sle e1) (sle e2)
		(* e1 --s-- e2 *)
		| LSetSub (e1, e2) -> Printf.sprintf "(%s --s-- %s)" (sle e1) (sle e2)


(* [def2 with #key := #k and #value := #v] *)
let string_of_unfold_info unfold_info =
	match unfold_info with
	| None -> ""
	| Some (id, unfold_info_list) ->
		let unfold_info_list =
			List.map (fun (v, le) -> "(" ^ v ^ " := " ^ (string_of_logic_expression le false) ^ ")") unfold_info_list in
		let unfold_info_list_str = String.concat " and " unfold_info_list in
		"[ " ^ id ^ " with " ^ unfold_info_list_str ^ " ]"


let rec string_of_lcmd lcmd =
	match lcmd with
	| Fold a                  -> "fold " ^ (string_of_logic_assertion a false)
	| Unfold (a, unfold_info) ->
		"unfold " ^ (string_of_logic_assertion a false) ^ (string_of_unfold_info unfold_info)
	| ApplyLem (lem_name, lparams) ->
	  let lparams_str = String.concat ", " (List.map (fun e -> string_of_logic_expression e false) lparams) in
		let lparams_str = if (not (lparams_str = "")) then (", " ^ lparams_str) else "" in
		"applyLemma " ^  lem_name ^ "(" ^ lparams_str ^ ")"
	| RecUnfold pred_name -> "unfold* " ^ pred_name
	| LogicIf (le, then_lcmds, else_lcmds) ->
		let le_str = string_of_logic_expression le false in
		let then_lcmds_str = String.concat "; " (List.map string_of_lcmd then_lcmds) in
		let else_lcmds_str = String.concat "; " (List.map string_of_lcmd else_lcmds) in
		let ret = if ((List.length else_lcmds) = 0)
			then "if (" ^ le_str ^ ") then { " ^ then_lcmds_str ^ " }"
			else "if (" ^ le_str ^ ") then { " ^ then_lcmds_str ^ " } else { " ^  else_lcmds_str ^ " }" in
		ret
	| Macro (name, lparams) ->
		let lparams_str = String.concat ", " (List.map (fun e -> string_of_logic_expression e false) lparams) in
		name ^ "(" ^ lparams_str ^ ")"
	| Assert a -> "assert " ^ (string_of_logic_assertion a false)


(** JSIL logic predicates *)
let rec string_of_predicate (predicate : jsil_logic_predicate) =
	let sle = fun e -> string_of_logic_expression e false in
	List.fold_left
		(fun acc_str (id, assertion) ->
			let id_str = match id with
			| None    -> ""
			| Some id -> "[" ^ id ^ "]" in
			acc_str ^ (Printf.sprintf "pred %s (%s) : %s %s;\n"
				predicate.name
				(String.concat ", " (List.map sle predicate.params))
				id_str
				(string_of_logic_assertion assertion false)))
		""
		predicate.definitions

let string_of_predicate_header pred_head =
	let name, params = pred_head in
	let sle = fun e -> string_of_logic_expression e false in
	let result = Printf.sprintf "%s (%s)" name (String.concat ", " (List.map sle params)) in
	result

(** JSIL All Statements *)
let string_of_cmd_aux sjsil_cmd i line_numbers_on escape_string str_tabs =
	let se = fun e -> string_of_expression e escape_string in
	let str_i = if line_numbers_on then (string_of_int i) ^ ". " else "" in
 	match sjsil_cmd with
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
					let var_arr_i_str = se var_arr.(i) in
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
					let var_arr_i_str = se var_arr.(i) in
					(if (i == 0)
						then loop 1 var_arr_i_str
						else  loop (i + 1) (str_ac ^ ", " ^ var_arr_i_str)) in
		let var_arr_str = loop 0 "" in
		Printf.sprintf "%s%s := PSI(%s)" str_i var var_arr_str


(** JSIL All Statements *)

let string_of_logic_metadata metadata str_tabs =
	let inv = metadata.invariant in
	let pre_lcmds = metadata.pre_logic_cmds in
	let post_lcmds = metadata.post_logic_cmds in
	let str_inv =
		  (match inv with
		  | None -> ""
		  | Some ass -> str_tabs ^ "[[" ^ string_of_logic_assertion ass false ^ "]]\n") in
	let str_pre_lcmds =
		if ((List.length pre_lcmds) > 0)
			then str_tabs ^ "[* " ^ (String.concat "; " (List.map string_of_lcmd pre_lcmds)) ^ " *]\n"
			else "" in
	let str_post_lcmds =
		if ((List.length post_lcmds) > 0)
			then str_tabs ^ "[+ " ^ (String.concat "; " (List.map string_of_lcmd post_lcmds)) ^ " +]"
			else ""  in
	str_inv ^ str_pre_lcmds, str_post_lcmds



let rec string_of_cmd sjsil_cmd tabs i line_numbers_on specs_on escape_string =
	let str_tabs = tabs_to_str tabs in
	let metadata, sjsil_cmd = sjsil_cmd in
	let str_pre, str_post = if specs_on then string_of_logic_metadata metadata str_tabs else "", "" in
	str_pre ^ (string_of_cmd_aux sjsil_cmd i line_numbers_on escape_string str_tabs) ^ str_post


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

(** JSIL Lemmas *)
let string_of_lemma (lemma_name : string) lemma =
	let f a = string_of_logic_assertion a false in 
	let f_list asrts = String.concat "; " (List.map f asrts) in 
  	let string_of_params          = (String.concat ", " lemma.lemma_spec.spec_params) in
	let string_of_pre             = "\t[[ " ^ (f (List.hd lemma.lemma_spec.proc_specs).pre) ^ " ]]\n" in
	let string_of_post            = "\t[[ " ^ (f_list (List.hd lemma.lemma_spec.proc_specs).post) ^ " ]]\n" in
	let string_of_proof =
		(match lemma.lemma_proof with
		  | None -> ""
			| Some lemma_proof -> "\t[* " ^ (String.concat ";\n\t   " (List.map string_of_lcmd lemma_proof)) ^ " *]\n") in
	"lemma " ^ lemma_name ^ "(" ^ string_of_params ^ ")\n" ^ string_of_pre ^ string_of_post ^ string_of_proof


let string_of_single_spec (prefix: string) (spec : jsil_single_spec) = 
	let f a = string_of_logic_assertion a false in 
	let f_list asrts = String.concat "; " (List.map f asrts) in 
	(prefix ^ "[[ " ^ (f spec.pre) ^ " ]]\n" ^
		prefix ^ "[[ " ^ (f_list spec.post) ^ " ]]\n" ^
		prefix ^ string_of_return_flag spec.ret_flag)


(** JSIL procedure specification *)
let string_of_specs (specs : jsil_single_spec list) =
	(String.concat ";\n " (List.map (string_of_single_spec "\t") specs)) ^ "\n"


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
	| SLBasic bcmd -> (string_of_bcmd bcmd 0 false false)
	(* goto j *)
  	| SLGoto j -> Printf.sprintf "goto %s" j
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
					let var_arr_i_str = se var_arr.(i) in
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
					let var_arr_i_str = se var_arr.(i) in
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
		let str_pre, str_post = string_of_logic_metadata metadata "\t\t\t" in
		let str_post = if (str_post <> "") then "\n" ^ str_post else str_post in
		let str_of_lab  =
			(match lab with
			| None -> "\t\t\t"
			| Some lab -> "\t" ^ lab ^ ":\t" ^ (if (String.length lab < 7) then "\t" else "")) in
		let str_of_lcmd  = string_of_lab_cmd lcmd in
		str := !str ^ str_pre ^ str_of_lab ^ str_of_lcmd ^ str_post ^ (if (i = len - 1) then "" else ";") ^ "\n"
	done;
	!str

(** Extended JSIL procedures spec *)
let string_of_ext_procedure_body proc =
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


(** Extended JSIL procedures *)
let string_of_ext_procedure proc =
	(* Optional specification block *)
	(match proc.lspec with
	| None -> ""
	| Some spec ->
		Printf.sprintf "spec %s (%s)\n %s\n" spec.spec_name (String.concat ", " spec.spec_params)
		  (string_of_specs spec.proc_specs))
	^
	(string_of_ext_procedure_body proc)


let string_of_jsil_spec spec =
	Printf.sprintf "spec %s (%s)\n %s" spec.spec_name (String.concat ", " spec.spec_params)
	(string_of_specs spec.proc_specs)

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
	(* Onlyspecs *)
	(Hashtbl.fold
		(fun _ spec acc_str -> acc_str ^ "\n" ^ "only " ^ (string_of_jsil_spec spec))
		program.onlyspecs
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
			if (ac = "\t") then (ac ^ a_str) else (ac ^ "\n\t" ^ a_str))
			"\t"
			a_list

let string_of_var_list var_lst =
	List.fold_left (fun ac v -> if (ac = "") then v else (ac ^ ", " ^ v)) "" var_lst

(* Explicit prints with constructors *)

(** Literals *)
let rec full_string_of_literal lit  =
	let sl = full_string_of_literal in
  match lit with
	| Undefined -> "Undefined"
	| Null -> "Null"
	| Empty -> "Empty"
	| Constant c -> string_of_constant c
	| Bool b ->
		(match b with
		| true -> "Bool true"
		| false -> "Bool false")
	| Num n -> "Num " ^ string_of_float n
	| String x -> Printf.sprintf "String \"%s\"" x
	| Loc loc -> "Loc " ^ loc
	| Type t -> "Type " ^ string_of_type t
	| LList ll ->
		(match ll with
		| [] -> "LList nil"
		| ll -> Printf.sprintf "LList [ %s ]" (String.concat ", " (List.map sl ll)))

(** JSIL logical expressions *)
let rec full_string_of_logic_expression e  =
  let sle = fun e -> full_string_of_logic_expression e in
  match e with
    | LLit llit -> let s = (full_string_of_literal llit) in "(LLit (" ^ s ^ "))"
	| LNone -> "LNone"
    | LVar lvar -> Printf.sprintf "(Lvar %s)" lvar
	| ALoc aloc -> Printf.sprintf "(Aloc %s)" aloc
	| PVar pvar -> Printf.sprintf "(Pvar %s)" pvar
	| LBinOp (e1, op, e2) -> Printf.sprintf "LBinOp (%s, %s, %s))" (sle e1) (string_of_binop op) (sle e2)
    | LUnOp (op, e) -> Printf.sprintf "(LUnOp (%s, %s))" (string_of_unop op) (sle e)
    | LTypeOf e -> Printf.sprintf "(LTypeOf (%s))" (sle e)
    | LEList list ->
		(match list with
		| [] -> "LEList [ ]"
		| ll -> Printf.sprintf "LEList [ %s ]" (String.concat ", " (List.map sle ll)))
	| LLstNth (e1, e2) -> Printf.sprintf "(LLstNth (%s, %s))" (sle e1) (sle e2)
	(* s-nth(e1, e2) *)
	| LStrNth (e1, e2) -> Printf.sprintf "(LStrNth (%s, %s))" (sle e1) (sle e2)


let string_of_heap (h : jsil_lit SHeap.t SHeap.t) =
	SHeap.fold
		(fun loc obj printed_heap ->
			  let printed_object =
					(SHeap.fold
						(fun prop hval print_obj ->
							let printed_hval = string_of_literal hval false in
							let printed_cell = Printf.sprintf "\n\t(cell '%s \"%s\" '%s)" loc prop printed_hval in
							print_obj ^ printed_cell)
						obj "") in
			printed_heap ^ (printed_object))
		h
		""


(* Shorthand *)
let print_type  t  = string_of_type t
let print_lexpr le = string_of_logic_expression le false
