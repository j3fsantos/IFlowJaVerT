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
	| SCall        of jsil_var  * jsil_expr  * jsil_expr list * int option

(* SJSIL procedures *)
type procedure = { 
    proc_name : string;
    proc_body : jsil_cmd array;
    proc_params : jsil_var list; 
		ret_label: int; 
		ret_var: jsil_var;
		error_label: (int option); 
		error_var: (jsil_var option);
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

(***** Alternative Syntax with Labels *****)

type jsil_lab_cmd =
  | SLBasic       of basic_jsil_cmd 
	| SLGoto        of string
	| SLGuardedGoto of jsil_expr * string     * string
	| SLCall        of jsil_var  * jsil_expr  * jsil_expr list * string option

(* SJSIL procedures *)
type lprocedure = { 
    lproc_name : string;
    lproc_body : ((string option * jsil_lab_cmd) array);
    lproc_params : jsil_var list; 
		lret_label: string; 
		lret_var: jsil_var;
		lerror_label: (string option); 
		lerror_var: (jsil_var option);
}

(***** Desugar me silly *****)

let desugar_labs (lproc : lprocedure) = 
	let ln, lb, lp, lrl, lrv, lel, lev = lproc.lproc_name, lproc.lproc_body, lproc.lproc_params, lproc.lret_label, lproc.lret_var, lproc.lerror_label, lproc.lerror_var in
	let nc = Array.length lb in
	
	let map_labels_to_numbers =
		let mapping = Hashtbl.create nc in
		for i = 0 to nc do
			(match lb.(i) with
			  | (Some str, _) -> Hashtbl.add mapping str i
				| _ -> ()); 
		done;
		mapping in
	
	let convert_to_sjsil mapping = 
		let cmds_nolab = Array.map (fun x -> (match x with | (_, cmd) -> cmd)) lb in
		let cmds = Array.map (fun x -> 
			match x with
			| SLBasic cmd -> SBasic cmd
			| SLGoto lab -> SGoto (Hashtbl.find mapping lab)
			| SLGuardedGoto (e, lt, lf) -> SGuardedGoto (e, Hashtbl.find mapping lt, Hashtbl.find mapping lf)
			| SLCall (x, e, le, ol) -> SCall (x, e, le, match ol with | None -> None | Some lab -> Some (Hashtbl.find mapping lab))
			) cmds_nolab in
		cmds, (Hashtbl.find mapping lrl), (match lel with | None -> None | Some lab -> Some (Hashtbl.find mapping lab)) in
	
	let mapping = map_labels_to_numbers in
	let b, rl, el = convert_to_sjsil mapping in
		{
			proc_name = ln;
    	proc_body = b;
    	proc_params = lp; 
			ret_label = rl; 
			ret_var = lrv;
			error_label = el; 
			error_var = lev
		}
