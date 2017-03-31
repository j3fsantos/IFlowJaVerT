(** JSIL_Syntax *)

open Set

(**/**)
(* Exceptions *)
exception Syntax_error of string
(**/**)

(** {2 Syntax of the JSIL language} *)

(** {b JSIL Types}. Can be associated with JSIL literals ({!type:jsil_lit}), 
    JSIL expressions ({!type:jsil_expr}), and JSIL logic expressions 
    ({!type:jsil_logic_expr}). *)
type jsil_type =
	| UndefinedType (** Type of Undefined *)
	| NullType      (** Type of Null      *)
	| EmptyType     (** Type of Empty     *)
	| NoneType      (** Type of None      *)
	| BooleanType   (** Type of booleans  *)
	| NumberType    (** Type of floats    *)
	| StringType    (** Type of strings   *)
	| ObjectType    (** Type of objects   *)
	| ListType      (** Type of lists     *)
	| TypeType      (** Type of types     *)

(** {b JSIL constants}. They are mostly inspired by those present in JavaScript's Math 
    and Date libraries. *)
type jsil_constant =
	| Min_float (** The smallest positive value *)
	| Max_float (** The largest positive finite value *) 
	| Random    (** A random number between 0 and 1 *)
	| E         (** {i e}, the base of natural logarithms *)
	| Ln10      (** Natural logarithm of 10 *)
	| Ln2       (** Natural logarithm of 2 *)
	| Log2e     (** Base-2 logarithm of {i e} *)
	| Log10e    (** Base-10 logarithm of {i e} *)
	| Pi        (** The number pi *)
	| Sqrt1_2   (** The square root of 1/2 *)
	| Sqrt2     (** The square root of 2 *)
	| UTCTime   (** Current UTC time *)
	| LocalTime (** Current local time *)

(** {b JSIL variables}. JSIL variables are internally represented as strings. *)
type jsil_var = string

(** {b JSIL literals}. The literal values of the JSIL language. Most are standard, some 
    are inherited from JavaScript. *)
type jsil_lit =
	| Undefined                  (** The literal [undefined] *)
	| Null                       (** The literal [null] *)
	| Empty                      (** The literal [empty] *)
	| Constant  of jsil_constant (** JSIL constants ({!type:jsil_constant}) *)
	| Bool      of bool          (** JSIL booleans: [true] and [false] *)
	| Num       of float         (** JSIL floats - double-precision 64-bit IEEE 754 *)
	| String    of string        (** JSIL strings *)
	| Loc       of string        (** JSIL object locations *)
	| Type      of jsil_type     (** JSIL types ({!type:jsil_type}) *)
	| LList     of jsil_lit list (** Lists of JSIL literals *)

(** {b JSIL unary operators}. JSIL features standard unary operators on numbers, booleans,
    lists, and strings, plus a variety of mathematical operators as well as a number of
    conversion operators between strings/numbers/integers. *)
type jsil_unop =
	(* Arithmetic *)
	| UnaryMinus  (** Unary minus *)
	(* Boolean *)
	| Not         (** Negation *)
	(* Bitwise *)
	| BitwiseNot  (** Bitwise negation *)
	(* Mathematics *)
	| M_abs       (** Absolute value *)
	| M_acos      (** Arccosine *)
	| M_asin      (** Arcsine *)
	| M_atan      (** Arctangent *)
	| M_ceil      (** Ceiling *)
	| M_cos       (** Cosine *)
	| M_exp       (** Exponentiation *)
	| M_floor     (** Flooring *)
	| M_log       (** Natural logarithm *)
	| M_round     (** Rounding *)
	| M_sgn       (** Sign *)
	| M_sin       (** Sine *)
	| M_sqrt      (** Square root *)
	| M_tan       (** Tangent *)
	(* Types *)
	| IsPrimitive (** Checks if the supplied expression is a primitive value *)
	| ToStringOp  (** Converts a number (integer or float) to a string *)
	| ToIntOp     (** Converts a float to an integer *)
	| ToUint16Op  (** Converts an integer to a 16-bit unsigned integer *)
	| ToUint32Op  (** Converts an integer to a 32-bit unsigned integer *)
	| ToInt32Op   (** Converts an integer to a 32-bit signed integer *)
	| ToNumberOp  (** Converts a string to a number *)
	(* Lists *)
	| Car         (** Head of a list *)
	| Cdr         (** Tail of a list *)
	| LstLen      (** List length *)
	(* Strings *)
	| StrLen      (** String length *)

(** {b JSIL binary operators}. JSIL features standard binary operators on numbers, 
    booleans, lists, and strings, plus several mathematical operators as well as a 
    subtyping operator *)
type jsil_binop =
	(* Comparison *)
	| Equal              (** Equality *)
	| LessThan           (** Less *)
	| LessThanEqual      (** Less or equal for numbers *)
	| LessThanString     (** Less or equal for strings *)
	(* Arithmetic *)
	| Plus               (** Addition *)
	| Minus              (** Subtraction *)
	| Times              (** Multiplication *)
	| Div                (** Float division *)
	| Mod                (** Modulus *)
	(* Boolean *)
	| And                (** Boolean conjunction *)
	| Or                 (** Boolean disjunction *)
	(* Bitwise *)
	| BitwiseAnd         (** Bitwise conjunction *)
	| BitwiseOr          (** Bitwise disjunction *)
	| BitwiseXor         (** Bitwise exclusive disjunction *)
	| LeftShift          (** Left bitshift *)
	| SignedRightShift   (** Signed right bitshift *)
	| UnsignedRightShift (** Unsigned right bitshift *)
	(* Mathematics *)
	| M_atan2            (** Arctangent y/x *)
	| M_pow              (** Power *)
	(* Lists *)
	| LstCons            (** List construction *)
	| LstCat             (** List concatenation *)
	(* Strings *)
	| StrCat             (** String concatenation *)

(** {b JSIL expressions}. Literals, variables, unary and binary operators, lists. *)
	type jsil_expr =
	| Literal  of jsil_lit                           (** JSIL literals ({!type:jsil_lit}) *)
	| Var      of jsil_var                           (** JSIL variables ({!type:jsil_var}) *)
	| BinOp    of jsil_expr * jsil_binop * jsil_expr (** Binary operators ({!type:jsil_binop}) *)
	| UnOp     of jsil_unop * jsil_expr              (** Unary operators ({!type:jsil_unop}) *)   
	| TypeOf   of jsil_expr	                         (** Typing operator *)   
	| LstNth   of jsil_expr	* jsil_expr	             (** Nth element of a list *)  
	| StrNth   of jsil_expr	* jsil_expr	             (** Nth element of a string *)               
	| EList    of jsil_expr list                     (** Lists of expressions *)
	| RAssume  of jsil_expr                          
	| RAssert  of jsil_expr
	| RNumSymb
	| RStrSymb

(**/**)
(* Shorthand *)
let lit_num n = Literal (Num n)
let lit_str s = Literal (String s)
let lit_loc l = Literal (Loc l)
let lit_typ t = Literal (Type t)
let lit_refv = lit_str "v"
let lit_refo = lit_str "o"
let rtype r = LstNth (r, lit_num 0.)
let base r = LstNth (r, lit_num 1.)
let field r = LstNth (r, lit_num 2.)
(**/**)

(** {b JSIL Basic Commands}. JSIL basic commands include the standard set of commands one 
    might expect of a language with extensible objects. *)
type jsil_basic_cmd =
	| SSkip                                            (** Empty command *)                         
	| SAssignment of jsil_var * jsil_expr              (** Assignment *)
	| SNew        of jsil_var                          (** Object creation *)
	| SLookup     of jsil_var * jsil_expr * jsil_expr  (** Field lookup *)
	| SMutation   of jsil_expr * jsil_expr * jsil_expr (** Field mutation *)
	| SDelete     of jsil_expr * jsil_expr             (** Field deletion *)
	| SDeleteObj  of jsil_expr                         (** Object deletion *)
	| SHasField   of jsil_var * jsil_expr * jsil_expr  (** Field check *)
	| SGetFields  of jsil_var * jsil_expr              (** All* fields of an object *)
	| SArguments  of jsil_var                          (** Arguments of the current function *)

(** {b JSIL Commands}. JSIL commands incorporate basic commands as well as commands that
    affect control flow, which are goto statements, function calls, and PHI-nodes, which
    offer direct support for SSA. *)
type jsil_cmd =
	| SBasic          of jsil_basic_cmd                                     (** JSIL basic commands *)
	| SGoto           of int                                                (** Unconditional goto *)
	| SGuardedGoto    of jsil_expr * int * int                              (** Conditional goto *)
	| SCall           of jsil_var * jsil_expr * jsil_expr list * int option (** Classical procedure call *)
	| SApply          of jsil_var * jsil_expr list * int option             (** Application-style procedure call *)
	| SPhiAssignment  of jsil_var * (jsil_expr array)                       (** PHI assignment *)
	| SPsiAssignment  of jsil_var * (jsil_expr array)

(** {2 Syntax of JSIL Logic} *)

(** {b JSIL logic variables}. JSIL logic variables are internally represented as strings. *)
type jsil_logic_var = string

(** {b JSIL logic expressions}. *)
type jsil_logic_expr =
	| LLit     of jsil_lit                                       (** JSIL literals ({!type:jsil_lit}) *)
	| LVar     of jsil_logic_var                                 (** JSIL logic variables ({!type:jsil_logic_var}) *)
	| ALoc     of string                                         (** Abstract locations *)
	| PVar     of jsil_var                                       (** JSIL program variables *)
	| LBinOp   of jsil_logic_expr * jsil_binop * jsil_logic_expr (** Binary operators ({!type:jsil_binop}) *)
	| LUnOp    of jsil_unop * jsil_logic_expr                    (** Unary operators ({!type:jsil_unop}) *)
	| LTypeOf  of jsil_logic_expr	                             (** Typing operator *) 
	| LLstNth  of jsil_logic_expr * jsil_logic_expr              (** Nth element of a list *)
	| LStrNth  of jsil_logic_expr * jsil_logic_expr              (** Nth element of a string *)              
	| LEList   of jsil_logic_expr list                           (** Lists of logical expressions *)
	| LNone                                                      (** Empty field value *)  
	| LUnknown                                                   (** Unknown field value *)

(** {b JSIL logic assertions}. *)
type jsil_logic_assertion =
	| LTrue                                                                    (** Logical true *)
	| LFalse                                                                   (** Logical false *)
	| LNot			    of jsil_logic_assertion                                (** Logical negation *)
	| LAnd			    of jsil_logic_assertion * jsil_logic_assertion         (** Logical conjunction *)
	| LOr		  	    of jsil_logic_assertion * jsil_logic_assertion         (** Logical disjunction *)
	| LEmp                                                                     (** Empty heap *)
	| LStar			    of jsil_logic_assertion * jsil_logic_assertion         (** Separating conjunction *)
	| LPointsTo	        of jsil_logic_expr * jsil_logic_expr * jsil_logic_expr (** Heap cell assertion *)
	| LPred			    of string * (jsil_logic_expr list)                     (** Predicates *)
	| LTypes		    of (jsil_logic_expr * jsil_type) list                  (** Typing assertion *)
	| LEmptyFields	    of jsil_logic_expr * (jsil_logic_expr list)            (** emptyFields assertion *)
	| LEq			    of jsil_logic_expr * jsil_logic_expr                   (** Expression equality *)
	| LLess			    of jsil_logic_expr * jsil_logic_expr                   (** Expression less-than for numbers *)
	| LLessEq		    of jsil_logic_expr * jsil_logic_expr                   (** Expression less-than-or-equal for numbers *)   
	| LStrLess	        of jsil_logic_expr * jsil_logic_expr                   (** Expression less-than for strings *)               

(** {b JSIL logic predicate}. *)
type jsil_logic_predicate = {
	name        : string;                    (** Name of the predicate *)
	num_params  : int;                       (** Number of parameters *)
	params      : jsil_logic_expr list;      (** Actual parameters *)
	definitions : jsil_logic_assertion list; (** Predicate definitions *)
}

(** {b Return flags for JSIL specifications}. *)
type jsil_return_flag =
	| Normal (** Normal return *)
	| Error  (** Error return *)

(** {b Single JSIL specifications}. *)
type jsil_single_spec = {
	pre      : jsil_logic_assertion; (** Precondition *)
	post     : jsil_logic_assertion; (** Postcondition *)
	ret_flag : jsil_return_flag      (** Return flag ({!type:jsil_return_flag}) *)
}

(** {b Full JSIL specifications}. *)
type jsil_spec = {
	spec_name    : string;               (** Procedure/spec name *)
	spec_params  : jsil_var list;        (** Procedure/spec parameters *) 
	proc_specs   : jsil_single_spec list (** List of single specifications *)
}

(**/**)
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
(**/**)

(** {b JSIL logic commands}. *)
type jsil_logic_command =
	| Fold             of jsil_logic_assertion                                                    (** Recursive fold *)
	| Unfold           of jsil_logic_assertion                                                    (** Single unfold *)
	| RecUnfold        of string                                                                  (** Recursive unfold of everything *)
	| LinearRecUnfold  of string * (jsil_logic_expr list)                                         (** Recursive unfold of everything but this time I will give you the arguments *)
	| LogicIf          of jsil_logic_expr * (jsil_logic_command list) * (jsil_logic_command list) (** If-then-else *)
	| Macro            of string * (jsil_logic_expr list)                                         (** Macro *)

(** {b JSIL logic macro}. *)
type jsil_logic_macro = {
	mname       : string;             (** Name of the macro *)
	mparams     : string list;        (** Actual parameters *)
	mdefinition : jsil_logic_command; (** Macro definition *)
}

(** {b JSIL metadata}. *)
type jsil_metadata = {
	line_offset     : int option;                  (** Better not to know what this is for *)
	invariant       : jsil_logic_assertion option; (** Invariant *)
	pre_logic_cmds  : jsil_logic_command list;     (** Logic commands preceding the command *)
	post_logic_cmds : jsil_logic_command list      (** Logic commands following the command *)
}

(**/**)
let empty_metadata = { line_offset = None; invariant = None; pre_logic_cmds = []; post_logic_cmds = [] }
(**/**)

(** {b JSIL procedures}. *)
type jsil_procedure = {
	proc_name    : string;                           (** Name *)
	proc_body    : (jsil_metadata * jsil_cmd) array; (** List of commands *)
	proc_params  : jsil_var list;                    (** Parameters *)
	ret_label    : int option;                       (** Return index *)
	ret_var      : jsil_var option;                  (** Return variable *)
	error_label  : int option;                       (** Error index *)
	error_var    : jsil_var option;                  (** Error variable *)
	spec         : jsil_spec option;                 (** Specification *)
}

(** {b JSIL Program}. *)
type jsil_program = (string, jsil_procedure) Hashtbl.t 

(**/**)

(***** Alternative Procedure Syntax with Labels *****)
type jsil_lab_cmd =
	| SLBasic          of jsil_basic_cmd
	| SLGoto           of string
	| SLGuardedGoto    of jsil_expr * string * string
	| SLCall           of jsil_var  * jsil_expr * jsil_expr list * string option
	| SLApply          of jsil_var  * jsil_expr list * string option
	| SLPhiAssignment  of jsil_var  * (jsil_expr array)
	| SLPsiAssignment  of jsil_var  * (jsil_expr array)

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
	imports : string list;
	(* Predicates = Name : String --> Definition *)
	predicates : (string, jsil_logic_predicate) Hashtbl.t;
	(* Specs = Name : String --> Spec *)
	onlyspecs : (string, jsil_spec) Hashtbl.t;
	(* JSIL extended procedures = Name : String --> Procedure *)
	procedures : (string, jsil_ext_procedure) Hashtbl.t;
	(* List of JSIL procedure names in order.*)
	procedure_names : (string list);
}

(*************************************)
(** JSIL Heaps                      **)
(*************************************)

let small_tbl_size = 31
let big_tbl_size = 1021

module SHeap = Hashtbl.Make(
	struct
		type t = string
		let equal = (=)
		let hash = Hashtbl.hash
	end)

let make_initial_heap is_big =
	let size = if (is_big) then big_tbl_size else small_tbl_size in
	let heap = SHeap.create size in
	heap

(** Basic functions **)

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


let macro_table     : (string, jsil_logic_macro) Hashtbl.t = Hashtbl.create 511

(* STATISTICS *)

let debug = ref false

let print_debug msg =
	if (!debug) then (print_endline msg)

let print_time msg =
	let time = Sys.time () in
	print_endline (msg ^ (Printf.sprintf " Time: %f" time))

let print_time_debug msg =
    if (!debug) then
	(let time = Sys.time () in
	print_endline (msg ^ (Printf.sprintf " Time: %f" time)))
	
(* SETS *)

module SS = Set.Make(String)

module MyInt =
 	struct
  	type t = int
    let compare = Pervasives.compare
  end

module MyNumber =
 	struct
  	type t = float
    let compare = Pervasives.compare
  end

module MyAssertion =
 	struct
  	type t = jsil_logic_assertion
    let compare = Pervasives.compare
  end

module SI = Set.Make(MyInt)
module SN = Set.Make(MyNumber)
module SA = Set.Make(MyAssertion)

(* Satisfiability cache *)
let check_sat_cache = Hashtbl.create 513 

let initialise = 
	Hashtbl.add check_sat_cache SA.empty true;
	Hashtbl.add check_sat_cache (SA.of_list [ LFalse ]) false

let statistics = Hashtbl.create 511

let update_statistics (fname : string) (time : float) = 
	if (Hashtbl.mem statistics fname)
		then let stat = Hashtbl.find statistics fname in
		Hashtbl.replace statistics fname (time :: stat)
		else Hashtbl.add statistics fname [ time ]
		
let process_statistics () =
	print_endline "\n STATISTICS \n ========== \n";
	print_endline (Printf.sprintf "Check sat cache: %d\n" (Hashtbl.length check_sat_cache));
	Hashtbl.iter (fun f lt -> 
		(* Calculate average, min, max *)
		let min = ref infinity in 
		let max = ref 0. in
		let tot = ref 0. in
		let avg = ref 0. in 
		let std = ref 0. in
		let len = float_of_int (List.length lt) in
		tot := List.fold_left (fun ac t -> 
			(if t < !min then min := t); (if t > !max then max := t);
			ac +. t) 0. lt;
		avg := !tot/.len;
		std := ((List.fold_left (fun ac t -> ac +. (!avg -. t) ** 2.) 0. lt) /. len) ** 0.5;
		print_endline (Printf.sprintf "\t%s\n" f);
		print_endline (Printf.sprintf "Tot: %f\tCll: %d\nMin: %f\tMax: %f\nAvg: %f\tStd: %f\n" !tot (int_of_float len) !min !max !avg !std)) statistics
(**/**)

(********************************************************)
(** Auxiliar functions for generating new program/logical
    variable names and new abstract locations          **)
(********************************************************)

let fresh_sth (name : string) : (unit -> string) =
  let counter = ref 0 in
  let rec f () =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f

let abs_loc_prefix = "_$l_"
let lvar_prefix = "_lvar_"
let pvar_prefix = "_pvar_"

let fresh_aloc = fresh_sth abs_loc_prefix
let fresh_lvar = fresh_sth lvar_prefix
let fresh_pvar = fresh_sth pvar_prefix

let fresh_lvar_from_lvar_name =
	let lvar_tbl = Hashtbl.create small_tbl_size in
	(fun (pred_name : string) (var : string) ->
		if (Hashtbl.mem lvar_tbl (pred_name, var))
			then (
				let i = Hashtbl.find lvar_tbl (pred_name, var) in
				Hashtbl.replace lvar_tbl (pred_name, var) (i + 1);
				var ^ "_" ^ (string_of_int i)
			) else
			(
				(* Printf.printf  "Could not find the pair (%s, %s) in the pred_lvar_tbl\n" pred_name var; *)
				Hashtbl.replace lvar_tbl (pred_name, var) 1;
				var ^ "_" ^ (string_of_int 0)
			))

let is_abs_loc_name (name : string) : bool =
	if ((String.length name) < 4)
		then false
		else ((String.sub name 0 4) = abs_loc_prefix)

let is_lvar_name (name : string) : bool =
	((String.sub name 0 1) = "#") || (((String.length name) > 6) && ((String.sub name 0 6) = lvar_prefix))

let is_pvar_name (name : string) : bool =
	(not ((is_abs_loc_name name) || (is_lvar_name name)))


(* A substitution type                                 *)
type substitution = ((string, jsil_logic_expr) Hashtbl.t)

let assertions_of_substitution (subst : substitution) = 
	Hashtbl.fold
		(fun v le ac -> (LEq (LVar v, le)) :: ac)
		subst
		[]

(* Typing Environment *)

type typing_environment        = ((string, jsil_type) Hashtbl.t)


let mk_gamma () = Hashtbl.create small_tbl_size

let gamma_get_type gamma var =
	try Some (Hashtbl.find gamma var) with Not_found -> None

let update_gamma (gamma : typing_environment) x te =
	(match te with
	| None -> Hashtbl.remove gamma x
	| Some te -> Hashtbl.replace gamma x te)

let weak_update_gamma (gamma : typing_environment) x te =
	(match te with
	| None -> ()
	| Some te -> Hashtbl.replace gamma x te)

let copy_gamma gamma =
	let new_gamma = Hashtbl.copy gamma in
	new_gamma

let extend_gamma gamma new_gamma =
	Hashtbl.iter
		(fun v t ->
			if (not (Hashtbl.mem gamma v))
				then Hashtbl.add gamma v t)
		new_gamma

let filter_gamma gamma vars =
	let new_gamma = Hashtbl.create small_tbl_size in
	Hashtbl.iter
		(fun v v_type ->
			(if (SS.mem v vars) then
				Hashtbl.replace new_gamma v v_type))
		gamma;
	new_gamma

let filter_gamma_with_subst gamma vars subst =
	let new_gamma = Hashtbl.create small_tbl_size in
	Hashtbl.iter
		(fun v v_type ->
			(if (List.mem v vars) then
				try
					match (Hashtbl.find subst v) with
					| LVar new_v -> Hashtbl.replace new_gamma new_v v_type
					| _ -> ()
				with Not_found -> ()))
		gamma;
	new_gamma

let get_gamma_vars catch_pvars gamma : SS.t =
	Hashtbl.fold
		(fun var _ ac -> 
			let is_lvar = is_lvar_name var in
			(match ((is_lvar && not catch_pvars) || (not is_lvar && catch_pvars)) with
			| true -> SS.add var ac
			| false -> ac))
		gamma SS.empty

let get_gamma_var_type_pairs gamma =
	Hashtbl.fold
		(fun var t ac_vars -> ((var, t) :: ac_vars))
		gamma
		[]

let rec gamma_substitution gamma subst partial =
	let new_gamma = Hashtbl.create 31 in
	Hashtbl.iter
		(fun var v_type ->
			try
			let new_var = Hashtbl.find subst var in
			(match new_var with
			| LVar new_var -> Hashtbl.replace new_gamma new_var v_type
			| _ ->
				(if (partial) then
					Hashtbl.add new_gamma var v_type))
			with _ ->
				(if (partial)
					then	Hashtbl.add new_gamma var v_type
					else (
						if (is_lvar_name var) then (
							let new_lvar = fresh_lvar () in
							Hashtbl.add subst var (LVar new_lvar);
							Hashtbl.add new_gamma new_lvar v_type
						))))
		gamma;
	new_gamma

let merge_gammas (gamma_l : typing_environment) (gamma_r : typing_environment) =
	Hashtbl.iter
		(fun var v_type ->
			if (not (Hashtbl.mem gamma_l var))
				then Hashtbl.add gamma_l var v_type)
		gamma_r

