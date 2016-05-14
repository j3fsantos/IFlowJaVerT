(***
 SJSIL - syntax
*)

(* jsil binary and unary operators *)
type bin_op = 
	(* comparison *)
  | Equal
  | LessThan
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

type unary_op = 
  | Not
  | Negative
  | ToStringOp
  | ToNumberOp
  | ToInt32Op
  | ToUint32Op
  | BitwiseNot


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

(* jsil literals *)
type jsil_lit =
	| Undefined
	| Null
	| Empty
	| Bool of bool
	| Num of float
	| String of string
  | Loc of string
  | Type of jsil_type
	| LVRef of string * string 
	| LORef of string * string 

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

(* SJSIL Basic statements *)
type basic_jsil_cmd =
  | SSkip	      
  | SAssignment    of jsil_var   * jsil_expr
	| SPhiAssignment of jsil_var   * (jsil_var array)
	| SNew           of jsil_var
	| SLookup        of jsil_var   * jsil_expr * jsil_expr
  | SMutation      of jsil_expr  * jsil_expr * jsil_expr
	| SDelete        of jsil_expr  * jsil_expr
	| SHasField      of jsil_var   * jsil_expr * jsil_expr
	| SProtoField    of jsil_var   * jsil_expr * jsil_expr
	| SProtoObj      of jsil_var   * jsil_expr * jsil_expr 

(* SJSIL All Statements *)
type jsil_cmd =
  | SBasic       of basic_jsil_cmd 
	| SGoto        of int
	| SGuardedGoto of jsil_expr * int        * int
	| SCall        of jsil_var  * jsil_expr  * jsil_expr list * int

(* SJSIL procedures *)
type procedure = { 
    proc_name : string;
    proc_body : jsil_cmd array;
    proc_params : jsil_var list; 
		ret_label: int; 
		ret_var: jsil_var;
		error_label: int; 
		error_var: jsil_var
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
		type t = string * string 
		let equal = (=)
		let hash = Hashtbl.hash
	end)

	

