(***
 SJSIL - syntax
*)

(* jsil binary and unary operators *)
type bin_op = 
	(* comparison *)
  | Equal
  | LessThan
	| LessThanString
  | LessThanEqual
	(* arithmetic operators *)
  | Plus
  | Minus
  | Times
  | Div
  | Mod
	(* subtyping operator for reference types *)
  | Subtype
	(* string concatenation *)
  | Concat
  (* Boolean Operators *)
	| And 
  | Or
	(* bitwise operators *)
  | BitwiseAnd
  | BitwiseOr
  | BitwiseXor
  | LeftShift
  | SignedRightShift
  | UnsignedRightShift
	(* Lists *)
	| LCons				
	(* Mathematics *)
	| M_atan2
	| M_pow

type unary_op = 
  | Not
  | Negative
	| IsPrimitive
  | ToStringOp
  | ToNumberOp
	| ToIntOp
	| ToUint16Op
  | ToInt32Op
  | ToUint32Op
  | BitwiseNot
  | Length
	(* UNARY OPERATORS FOR LISTS *)
	| Car
	| Cdr
	(* Mathematics *)
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

(* constants *)
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

(* jsil types *)
type jsil_type =
  | NullType
  | UndefinedType
	| EmptyType
  | BooleanType
  | StringType
  | NumberType
  | ObjectType 
	| ReferenceType
	| ObjectReferenceType
	| VariableReferenceType
	| TypeType
	(* LIST TYPE *)
	| ListType

(* jsil literals *)
type jsil_lit =
	| Undefined
	| Null
	| Empty
	| Constant of constant
	| Bool of bool
	| Num of float
	| String of string
  | Loc of string
  | Type of jsil_type
	| LVRef of jsil_lit * string 
	| LORef of jsil_lit * string 
	(* LISTS (FOR DESCRIPTORS) *)
	| LList of jsil_lit list

(* jsil expressions *)
type jsil_var = string

type jsil_expr = 
  | Literal of jsil_lit
  | Var of jsil_var
  | BinOp of jsil_expr * bin_op * jsil_expr
  | UnaryOp of unary_op * jsil_expr
  | VRef of jsil_expr * jsil_expr
  | ORef of jsil_expr * jsil_expr
  | Base of jsil_expr
  | Field of jsil_expr
  | TypeOf of jsil_expr
	(* LISTS (FOR DESCRIPTORS) *)
	| LEList of jsil_expr list
	| LLNth of jsil_expr * jsil_expr

(* jsil logical expressions *)
type jsil_logic_var = string

type jsil_logic_expr =
	| LLit				of jsil_lit
	| LNone
	| LListEmpty
	| LVar				of jsil_logic_var
	| LLVar				of jsil_logic_var
	| PVar				of jsil_var
	| LBinOp			of jsil_logic_expr * bin_op * jsil_logic_expr
	| LUnOp				of unary_op * jsil_logic_expr
	| LEVRef			of jsil_logic_expr * jsil_logic_expr
	| LEORef			of jsil_logic_expr * jsil_logic_expr
	| LBase				of jsil_logic_expr
	| LField			of jsil_logic_expr
	| LTypeOf			of jsil_logic_expr
	| LLCons      of jsil_logic_expr * jsil_logic_expr

type jsil_logic_assertion =
	| LAnd				of jsil_logic_assertion * jsil_logic_assertion
	| LOr					of jsil_logic_assertion * jsil_logic_assertion
	| LNot				of jsil_logic_assertion
	| LTrue
	| LFalse
	| LEq					of jsil_logic_expr * jsil_logic_expr
	| LLessEq			of jsil_logic_expr * jsil_logic_expr
	| LStar				of jsil_logic_assertion * jsil_logic_assertion
	| LPointsTo		of jsil_logic_expr * jsil_logic_expr * jsil_logic_expr
	| LEmp
	| LExists			of (jsil_logic_var list) * jsil_logic_assertion
	| LForAll			of (jsil_logic_var list) * jsil_logic_assertion

type jsil_return_flag =
	| Normal
	| Error

type jsil_single_spec = {
	  pre : jsil_logic_assertion; 
		post : jsil_logic_assertion; 
		ret_flag : jsil_return_flag 
}

type jsil_spec = { 
    spec_name : string;
    spec_params : jsil_var list; 
		proc_specs : jsil_single_spec list
}

type jsil_n_single_spec = {
	  n_pre :  ((string, ((jsil_logic_expr * jsil_logic_expr) list)) Hashtbl.t) * ((string, jsil_logic_expr) Hashtbl.t) * (jsil_logic_assertion DynArray.t); 
		n_post : ((string, ((jsil_logic_expr * jsil_logic_expr) list)) Hashtbl.t) * ((string, jsil_logic_expr) Hashtbl.t) * (jsil_logic_assertion DynArray.t); 
		n_ret_flag : jsil_return_flag 
}

type jsil_n_spec = { 
    n_spec_name : string;
    n_spec_params : jsil_var list; 
		n_proc_specs : jsil_n_single_spec list
}

(* SJSIL Basic statements *)
type basic_jsil_cmd =
  | SSkip	      
  | SAssignment    of jsil_var  * jsil_expr
	| SPhiAssignment of jsil_var  * (jsil_var option array)
	| SNew           of jsil_var
	| SLookup        of jsil_var  * jsil_expr * jsil_expr
  | SMutation      of jsil_expr * jsil_expr * jsil_expr
	| SDelete        of jsil_expr * jsil_expr
	| SHasField      of jsil_var  * jsil_expr * jsil_expr
	| SProtoField    of jsil_var  * jsil_expr * jsil_expr
	| SProtoObj      of jsil_var  * jsil_expr * jsil_expr 
	| SGetFields     of jsil_var  * jsil_expr

(* SJSIL All Statements *)
type jsil_cmd =
  | SBasic       of basic_jsil_cmd 
	| SGoto        of int
	| SGuardedGoto of jsil_expr * int        * int
	| SCall        of jsil_var  * jsil_expr  * jsil_expr list * int option

(* SJSIL procedures *)
type procedure = { 
    proc_name : string;
    proc_body : (jsil_logic_assertion option * jsil_cmd) array;
    proc_params : jsil_var list; 
		ret_label: int; 
		ret_var: jsil_var;
		error_label: (int option); 
		error_var: (jsil_var option);
		spec: jsil_spec option;
}

(* SJSIL Program *)
 module SProgram = Hashtbl.Make(
	struct
		type t = string  
		let equal = (=)
		let hash = Hashtbl.hash
	end)


(* SJSIL Heaps *)
 module SHeap = Hashtbl.Make(
	struct
		type t = string	
		let equal = (=)
		let hash = Hashtbl.hash
	end)
	
(** 
 * We use integers to represent both abstract and concrete locations
*)

type abstract_heap = {
	aheap: (string, ((jsil_logic_expr * jsil_logic_expr) list)) Hashtbl.t; 
	mutable count: int; 
	parent: abstract_heap option  
}

(***** Alternative Procedure Syntax with Labels *****)

type jsil_lab_cmd =
  | SLBasic       of basic_jsil_cmd 
	| SLGoto        of string
	| SLGuardedGoto of jsil_expr * string     * string
	| SLCall        of jsil_var  * jsil_expr  * jsil_expr list * string option

(* SJSIL procedures with string labels *)
 module SLProgram = Hashtbl.Make(
	struct
		type t = string  
		let equal = (=)
		let hash = Hashtbl.hash
	end)


type lprocedure = { 
    lproc_name : string;
    lproc_body : ((jsil_logic_assertion option * string option * jsil_lab_cmd) array);
    lproc_params : jsil_var list; 
		lret_label: string; 
		lret_var: jsil_var;
		lerror_label: (string option); 
		lerror_var: (jsil_var option);
		lspec: jsil_spec option;
}

type jsil_lprog = (string list option) * (lprocedure SLProgram.t) 