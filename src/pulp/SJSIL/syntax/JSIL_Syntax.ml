(***
 SJSIL - types
*)

exception Syntax_error of string

(* JSIL types *)
type jsil_type =
	| UndefinedType
	| NullType
	| EmptyType
	| NoneType
	| BooleanType
	| IntType
	| NumberType
	| StringType
	| ObjectType
	| ListType
	| TypeType

(* JSIL constants *)
type constant =
	| Min_float
	| Max_float
	| Random
	| E
	| Ln10
	| Ln2
	| Log2e
	| Log10e
	| Pi
	| Sqrt1_2
	| Sqrt2
	| UTCTime
	| LocalTime

(* JSIL literals *)
type jsil_lit =
	| Undefined
	| Null
	| Empty
	| Constant of constant
	| Bool     of bool
	| Integer  of int
	| Num      of float
	| String   of string
  | Loc      of string
  | Type     of jsil_type
	(* List of literals (for descriptors) *)
	| LList    of jsil_lit list

(* JSIL variables *)
type jsil_var = string

(* JSIL binary operators *)
type bin_op =
	(* Comparison *)
  | Equal
  | LessThan
	| LessThanEqual
	| LessThanString
	(* Arithmetic operators *)
  | Plus
  | Minus
  | Times
  | Div
  | Mod
  (* Boolean operators *)
	| And
  | Or
	(* Bitwise operators *)
  | BitwiseAnd
  | BitwiseOr
  | BitwiseXor
  | LeftShift
  | SignedRightShift
  | UnsignedRightShift
	(* Mathematics *)
	| M_atan2
	| M_pow
	(* List manipulation *)
	| LstCons
	| LstCat
	(* String manipulation *)
  | StrCat
	(* Types *)
	| SubType

(* JSIL unary operators *)
type unary_op =
	(* Arithmetic operators *)
  | UnaryMinus
	(* Boolean operators *)
  | Not
	(* Bitwise operators *)
	| BitwiseNot
	(* Mathematics *)
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
	| M_sgn
	| M_sin
	| M_sqrt
	| M_tan
	(* Type checking and conversion *)
	| IsPrimitive
  | ToStringOp
	| ToIntOp
	| ToUint16Op
  | ToInt32Op
  | ToUint32Op
	| ToNumberOp
	(* List manipulation *)
	| Car
	| Cdr
	| LstLen
	(* String manipulation *)
	| StrLen

(* JSIL expressions *)
type jsil_expr =
  | Literal  of jsil_lit
  | Var      of jsil_var
  | BinOp    of jsil_expr * bin_op * jsil_expr
  | UnaryOp  of unary_op * jsil_expr
  | TypeOf   of jsil_expr
	| RAssume  of jsil_expr
	| RAssert  of jsil_expr
	| RNumSymb
	| RStrSymb
	(* List of expressions (for descriptors) *)
	| EList    of jsil_expr list
	| LstNth   of jsil_expr * jsil_expr
	| StrNth   of jsil_expr * jsil_expr

(* Shorthand *)
let lit_int i = Literal (Integer i)
let lit_num n = Literal (Num n)
let lit_str s = Literal (String s)
let lit_loc l = Literal (Loc l)
let lit_typ t = Literal (Type t)

let lit_refv = lit_str "v"
let lit_refo = lit_str "o"
let rtype  r = LstNth (r, lit_int 0)
let base  r = LstNth (r, lit_int 1)
let field r = LstNth (r, lit_int 2)

(* JSIL Basic statements *)
type jsil_basic_cmd =
  | SSkip
  | SAssignment     of jsil_var  * jsil_expr
	| SNew            of jsil_var
	| SLookup         of jsil_var  * jsil_expr * jsil_expr
  | SMutation       of jsil_expr * jsil_expr * jsil_expr
	| SDelete         of jsil_expr * jsil_expr
	| SHasField       of jsil_var  * jsil_expr * jsil_expr
	| SGetFields      of jsil_var  * jsil_expr
	| SArguments      of jsil_var

(* JSIL All Statements *)
type jsil_cmd =
  | SBasic          of jsil_basic_cmd
	| SGoto           of int
	| SGuardedGoto    of jsil_expr * int        * int
	| SCall           of jsil_var  * jsil_expr  * jsil_expr list * int option
	| SApply          of jsil_var  * jsil_expr list * int option
	| SPhiAssignment  of jsil_var  * (jsil_var option array)
	| SPsiAssignment  of jsil_var  * (jsil_var option array)

(* JSIL logical expressions *)
type jsil_logic_var = string
type jsil_logic_expr =
	| LLit				of jsil_lit
	| LNone
	| LVar				of jsil_logic_var
	| ALoc				of string
	| PVar				of jsil_var
	| LBinOp			of jsil_logic_expr * bin_op * jsil_logic_expr
	| LUnOp				of unary_op * jsil_logic_expr
	| LTypeOf			of jsil_logic_expr
	| LEList      of jsil_logic_expr list
	| LLstNth     of jsil_logic_expr * jsil_logic_expr
	| LStrNth     of jsil_logic_expr * jsil_logic_expr
	| LUnknown

(* JSIL logic assertions *)
type jsil_logic_assertion =
	| LAnd				of jsil_logic_assertion * jsil_logic_assertion
	| LOr					of jsil_logic_assertion * jsil_logic_assertion
	| LNot				of jsil_logic_assertion
	| LTrue
	| LFalse
	| LEq					of jsil_logic_expr * jsil_logic_expr
	| LLess	   		of jsil_logic_expr * jsil_logic_expr
	| LLessEq	   	of jsil_logic_expr * jsil_logic_expr
	| LStrLess    of jsil_logic_expr * jsil_logic_expr
	| LStar				of jsil_logic_assertion * jsil_logic_assertion
	| LPointsTo		of jsil_logic_expr * jsil_logic_expr * jsil_logic_expr
	| LEmp
(*| LExists			of (jsil_logic_var list) * jsil_logic_assertion
	| LForAll			of (jsil_logic_var list) * jsil_logic_assertion *)
	| LPred				of string * (jsil_logic_expr list)
	| LTypes      of (jsil_logic_expr * jsil_type) list

(* JSIL logic predicates *)
type jsil_logic_predicate = {
	name        : string;
	num_params  : int;
	params      : jsil_logic_expr list;
	definitions : jsil_logic_assertion list;
}

(* JSIL spec return flag *)
type jsil_return_flag =
	| Normal
	| Error

(* JSIL procedure specification *)
type jsil_single_spec = {
	pre      : jsil_logic_assertion;
	post     : jsil_logic_assertion;
	ret_flag : jsil_return_flag
}

type jsil_spec = {
	spec_name    : string;
	spec_params  : jsil_var list;
	proc_specs   : jsil_single_spec list
}

let create_single_spec pre post flag =
	{
		pre      = pre;
		post     = post;
		ret_flag = flag
	}

let create_jsil_spec name params specs =
	{
		spec_name   = name;
		spec_params = params;
		proc_specs  = specs
	}

(* JSIL logic commands *)
type jsil_logic_command =
	| Fold       of jsil_logic_assertion
	| Unfold     of jsil_logic_assertion
	| RecUnfold  of string

(* JSIL command metadata *)
type jsil_metadata = {
	line_offset : int option;
	pre_cond    : jsil_logic_assertion option;
	logic_cmds  : jsil_logic_command list;
}

let empty_metadata = { line_offset = None; pre_cond = None; logic_cmds = [] }

(* JSIL procedures *)
type jsil_procedure = {
    proc_name    : string;
    proc_body    : (jsil_metadata * jsil_cmd) array;
    proc_params  : jsil_var list;
		ret_label    : int option;
		ret_var      : jsil_var option;
		error_label  : int option;
		error_var    : jsil_var option;
		spec         : jsil_spec option;
}

(* JSIL Program = Name : String --> Procedure *)
type jsil_program = (string, jsil_procedure) Hashtbl.t


(***** Alternative Procedure Syntax with Labels *****)
type jsil_lab_cmd =
  | SLBasic          of jsil_basic_cmd
	| SLGoto           of string
	| SLGuardedGoto    of jsil_expr * string                    * string
	| SLCall           of jsil_var  * jsil_expr                 * jsil_expr list * string option
	| SLApply          of jsil_var  * jsil_expr list            * string option
	| SLPhiAssignment  of jsil_var  * (jsil_var option array)
	| SLPsiAssignment  of jsil_var  * (jsil_var option array)

(* JSIL procedures extended with string labels *)
type jsil_ext_procedure = {
    lproc_name : string;
    lproc_body : ((jsil_metadata * string option * jsil_lab_cmd) array);
    lproc_params : jsil_var list;
		lret_label: string option;
		lret_var: jsil_var option;
		lerror_label: string option;
		lerror_var: jsil_var option;
		lspec: jsil_spec option;
}

(* Extended JSIL program type *)
type jsil_ext_program = {
	(* Import statements = [Filename : String] *)
  imports    : string list;
	(* Predicates = Name : String --> Definition *)
	predicates : (string, jsil_logic_predicate) Hashtbl.t;
	(* JSIL extended procedures = Name : String --> Procedure *)
	procedures : (string, jsil_ext_procedure) Hashtbl.t;
}



(** Basic functions **)

let types_lub t1 t2 =
	match t1, t2 with
	| UndefinedType, UndefinedType -> Some UndefinedType
	| NullType, NullType -> Some NullType
	| EmptyType, EmptyType -> Some EmptyType
	| NoneType, NoneType -> Some NoneType
	| BooleanType, BooleanType -> Some BooleanType
	| IntType, IntType -> Some IntType
	| IntType, NumberType -> Some NumberType
	| NumberType, NumberType -> Some NumberType
	| NumberType, IntType -> Some NumberType
	| StringType, StringType -> Some StringType
	| ObjectType, ObjectType -> Some ObjectType
	| ListType, ListType -> Some ListType
	| TypeType, TypeType -> Some TypeType
	| _, _ -> None

let types_leq t1 t2 =
	let t = types_lub t1 t2 in
	match t with
	| Some t -> (t = t2)
	| None -> false


let proc_get_ret_var proc ret_flag =
	let ret_var =
		match ret_flag with
		| Normal -> proc.ret_var
		| Error -> proc.error_var in
	match ret_var with
	| Some ret_var -> ret_var
	| None -> raise (Failure "proc_get_ret_var: fatal error")

let get_proc prog proc_name =
	try
		Hashtbl.find prog proc_name
	with _ ->
		raise (Failure "get_proc: fatal error")

let get_proc_args proc = proc.proc_params

let get_proc_cmd proc i =
	proc.proc_body.(i)

let debug = ref false

let print_debug msg =
	if (!debug) then print_endline msg
