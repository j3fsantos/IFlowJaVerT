open SSyntax

(***
 S-Expression Serialization
*)
let string_of_float x = 
	if (x == nan) 
		then "+nan.0"
		else if (x == neg_infinity) 
						then "-inf.0"
						else if (x == infinity) 
									then "+inf.0"
									else string_of_float x 
(**	
the following does not work because nan is interpreted as a variable
 match x with 
	| nan -> "+nan.0"
	| neg_infinity -> "-inf.0"
	| infinity -> "+inf.0"
	| _ -> string_of_float x
*)

let string_of_binop bop =
	match bop with
  | Equal -> "="
  | LessThan -> "<"
  | LessThanEqual -> "<=" 
 	| Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Div -> "/"
  | Mod -> "%"
	| Subtype -> "<:"
	| Concat -> "concat"
	| And -> "and"
  | Or -> "or"
	| BitwiseAnd -> "&"
  | BitwiseOr -> "|"
  | BitwiseXor -> "^"
  | LeftShift -> "<<"
  | SignedRightShift -> ">>"
  | UnsignedRightShift -> ">>>"

let string_of_unop uop = match uop with 
  | Not -> "not"
  | Negative -> "-"
	| ToStringOp -> "num_to_string"
  | ToNumberOp -> "string_to_num"
  | ToInt32Op -> "num_to_int32"
  | ToUint32Op -> "num_to_unit32"
  | BitwiseNot -> "!"

let string_of_bool x =
  match x with
    | true -> "#t"
    | false -> "#f"

let string_of_type t =
  match t with
  | NullType -> "$$null"
  | UndefinedType -> "$$undefined"
  | BooleanType -> "$$boolean_type"
  | StringType -> "$$string_type"
  | NumberType -> "$$number_type"
  | ObjectType -> "$$object_type"
  | ReferenceType -> "$$reference_type"
	| ObjectReferenceType -> "$$o_reference_type"
	| VariableReferenceType -> "$$v_reference_type"	


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
		| LVRef (field, value) -> Printf.sprintf "vref(%s, %s)" (string_of_literal field escape_string) value
		| LORef (field, value) -> Printf.sprintf "oref(%s, %s)" (string_of_literal field escape_string) value


let rec string_of_logic_expression e escape_string =
  let sle = fun e -> string_of_logic_expression e escape_string in
  match e with
    | LLit llit -> string_of_literal llit escape_string
		| LNone -> "none"
    | LVar lvar -> lvar
		| LLVar llvar -> llvar
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

let string_of_list list =
	match list with
	| [] -> ""
	| elem :: rest ->
  	List.fold_left 
  		(fun prev_elems elem -> prev_elems ^ ", " ^ elem) elem rest	

let string_of_lvar_list list =
	match list with
	| [] -> ""
	| elem :: rest ->
  	List.fold_left 
  		(fun prev_elems elem -> prev_elems ^ ", " ^ elem) elem rest	

let rec string_of_logic_assertion a escape_string =
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
		| LExists (lvars, a) -> Printf.sprintf "exists %s . %s" (string_of_lvar_list lvars) (sla a)
		(* forall vars . a *)
		| LForAll (lvars, a) -> Printf.sprintf "forall %s . %s" (string_of_lvar_list lvars) (sla a)

let string_of_return_flag flag =
	match flag with
		| Normal -> Printf.sprintf "normal"
		| Error -> Printf.sprintf "error"

let string_of_jsil_single_spec spec =
	Printf.sprintf "\tPre: %s,\n\tPost: %s,\n\tFlag: %s\n"
		(string_of_logic_assertion spec.pre false)
		(string_of_logic_assertion spec.post false)
		(string_of_return_flag spec.ret_flag)

let rec string_of_jsil_spec_list list =
	match list with
		| [] -> ""
		| spec :: rest -> (string_of_jsil_single_spec spec) ^ (string_of_jsil_spec_list rest)

(*
  spec xpto (arg1, arg2, ...) { 
		pre: ...,
		post: ...,
		flag: normal|error,
		pre: ...,
		post: ...,
		flag: normal|error,
		...
	}
*)
let string_of_spec spec =			
	Printf.sprintf "spec %s (%s)\n%s" 
  	spec.spec_name 
   	(string_of_list spec.spec_params) 
		(string_of_jsil_spec_list spec.proc_specs)


let string_of_shallow_symb_heap heap = 
	LHeap.fold
		(fun loc (fv_pairs, default_value) ac -> 
			let str_fv_pairs = 
				List.fold_left
					(fun ac (field, value) ->
						let field_str = string_of_logic_expression field false in 
						let value_str = string_of_logic_expression value false in 
						let field_value_str = "(" ^ field_str ^ ": " ^ value_str ^ ")"  in 
						if (ac = "") 
							then field_value_str 
							else ac ^ ", " ^ field_value_str)
					""
					fv_pairs in 
			let default_value_str = 
				(match default_value with 
				| None -> ""
				| Some lexpr ->
					let lexpr_str = string_of_logic_expression lexpr false in 
					"(default: " ^ lexpr_str ^ ")") in 
			let symb_obj_str = 
				(if (str_fv_pairs = "") 
					then loc ^ " |-> [" ^  default_value_str ^ "]" 
					else loc ^ " |-> [" ^  str_fv_pairs ^ ", " ^ default_value_str ^ "]") in 
			if (ac = "") then symb_obj_str else ac ^ ", " ^ symb_obj_str)
		heap
		""
		
		
let string_of_shallow_symb_store store = 
	Hashtbl.fold 
		(fun var v_val ac ->
			 let v_val_str = string_of_logic_expression v_val false in 
			 let var_val_str = "(" ^ var ^ ": " ^ v_val_str ^ ")" in 
			if (ac = "") then var_val_str else ac ^ ", " ^ var_val_str )
		store
		""


let string_of_shallow_p_formulae p_formulae = 
	DynArray.fold_left
		(fun ac cur_ass -> 
			let cur_ass_str = string_of_logic_assertion cur_ass false in 
			if (ac = "") then cur_ass_str else ac ^ ", " ^ cur_ass_str)
		""
		p_formulae


let string_of_shallow_symb_state heap store p_formulae = 
	let str = "Symbolic State: \n" in 
	let str_heap = "\t Heap: " ^ (string_of_shallow_symb_heap heap) ^ "\n" in 
	let str_store = "\t Store: " ^ (string_of_shallow_symb_store store) ^ "\n" in 
	let str_p_formulae = "\t Pure Formulae: " ^ (string_of_shallow_p_formulae p_formulae) ^ "\n" in 
	str ^ str_heap ^ str_store ^ str_p_formulae 

(* spec xpto (x, y) pre: assertion, post: assertion, flag: NORMAL|ERROR *) 
let string_of_n_spec spec = 
	let spec_name = spec.n_spec_name in 
	let spec_params = spec.n_spec_params in 
	let pre_post_list = spec.n_proc_specs in
	let params_str = 
		List.fold_left
			(fun ac param -> if (ac = "") then param else ac ^ ", " ^ param)
			""
			spec_params in
	let str = "Specs for " ^ spec_name ^ " (" ^ params_str ^ "): \n" in 
	let pre_post_list_str =
		List.fold_left
			(fun ac single_spec -> 
				let pre_heap, pre_store, pre_p_formulae = single_spec.n_pre in 
				let post_heap, post_store, post_p_formulae = single_spec.n_post in 
				let ret_flag = single_spec.n_ret_flag in 
				let pre_str = string_of_shallow_symb_state pre_heap pre_store pre_p_formulae in 
				let post_str = string_of_shallow_symb_state post_heap post_store post_p_formulae in 
				let ret_flag_str = 
					(match ret_flag with 
					| Normal -> "normal"
					| Error -> "error") in 
				let single_spec_str = "Single Spec - " ^ ret_flag_str ^ "\n Pre " ^ pre_str ^ "Post " ^ post_str in 
				if (ac = "") then single_spec_str else ac ^ single_spec_str)
			""
			pre_post_list in
		str ^ pre_post_list_str 


let string_of_n_spec_table spec_table = 
	Hashtbl.fold 
		(fun spec_name spec ac -> 
			let spec_str = string_of_n_spec spec in 
			if ac = "" then spec_str else ac ^ "----------\n" ^ spec_str)
		spec_table
		""
	
			
	
	
	
	
	
