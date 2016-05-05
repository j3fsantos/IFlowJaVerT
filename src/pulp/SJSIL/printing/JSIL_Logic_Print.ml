open SSyntax
open JSIL_Logic_Syntax

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

let string_of_literal lit escape_string =
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

let string_of_logic_val lval escape_string =
	match lval with
	| LLit lit -> string_of_literal lit escape_string
	| LNone -> "none"
	| LListEmpty -> "[]"

let rec string_of_logic_expression e escape_string =
  let sle = fun e -> string_of_logic_expression e escape_string in
  match e with
    | LVal lval -> string_of_logic_val lval escape_string
    | LVar lvar -> Pulp_Syntax_Print.string_of_var lvar
		| PVar pvar -> Pulp_Syntax_Print.string_of_var pvar
		(* (e1 bop e2) *)
    | LBinOp (e1, op, e2) -> Printf.sprintf "(%s %s %s)" (sle e1) (string_of_binop op) (sle e2)
		(* (uop e1 e2) *)
    | LUnOp (op, e) -> Printf.sprintf "(%s %s)" (string_of_unop op) (sle e)
		(* v-ref(e1, e2) *)
    | LVRef (e1, e2) -> Printf.sprintf "v-ref(%s, %s)" (sle e1) (sle e2)
  	(* o-ref(e1, e2) *)
    | LORef (e1, e2) -> Printf.sprintf "o-ref(%s, %s)" (sle e1) (sle e2)
		(* base(e) *)
    | LBase e -> Printf.sprintf "base(%s)" (sle e)
		(* field(e) *)
    | LField e -> Printf.sprintf "field(%s)" (sle e)
		(* typeof(e) *)
    | LTypeOf e -> Printf.sprintf "typeof(%s)" (sle e)
		(* e1 :: e2*)
		| LCons (e1, e2) -> Printf.sprintf "%s :: %s" (sle e1) (sle e2)

let string_of_list list =
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
		| LPointTo (e1, e2, e3) -> Printf.sprintf "(%s, %s) -> %s" (sle e1) (sle e2) (sle e3)
		(* emp *)
		| LEmp -> Printf.sprintf "emp"
		(* exists vars . a *)
		| LExists (lvars, a) -> Printf.sprintf "exists %s . %s" (string_of_list lvars) (sla a)
		(* forall vars . a *)
		| LForAll (lvars, a) -> Printf.sprintf "forall %s . %s" (string_of_list lvars) (sla a)

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
