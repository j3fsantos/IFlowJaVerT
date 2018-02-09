open CCommon

(** JSIL_Syntax *)

(** {2 Syntax of the JSIL language} *)

(** {b JSIL variables}. JSIL variables are internally represented as strings. *)
type jsil_var = string [@@deriving show]

(** {b JSIL expressions}. Literals, variables, unary and binary operators, lists. *)
	type jsil_expr =
	| Literal  of Literal.t                       (** JSIL literals ({!type:Literal.t}) *)
	| Var      of jsil_var                        (** JSIL variables ({!type:jsil_var}) *)
	| BinOp    of jsil_expr * BinOp.t * jsil_expr (** Binary operators ({!type:BinOp.t}) *)
	| UnOp     of UnOp.t * jsil_expr              (** Unary operators ({!type:UnOp.t}) *)
	| LstNth   of jsil_expr	* jsil_expr	          (** Nth element of a list *)
	| StrNth   of jsil_expr	* jsil_expr	          (** Nth element of a string *)
	| EList    of jsil_expr list                  (** Lists of expressions *)
	| ESet     of jsil_expr list                  (** Sets of expressions *)
	| SetUnion of jsil_expr list
	| SetInter of jsil_expr list

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
	| Skip                                                                    (** Empty command *)
	| Assignment of jsil_var * jsil_expr                                      (** Assignment *)
	| New        of jsil_var * (jsil_expr option)                             (** Object creation *)
	| Lookup     of jsil_var * jsil_expr * jsil_expr                          (** Field lookup *)
	| Mutation   of jsil_expr * jsil_expr * jsil_expr * (Permission.t option) (** Field mutation *)
	| Delete     of jsil_expr * jsil_expr                                     (** Field deletion *)
	| DeleteObj  of jsil_expr                                                 (** Object deletion *)
	| HasField   of jsil_var * jsil_expr * jsil_expr                          (** Field check *)
	| GetFields  of jsil_var * jsil_expr                                      (** All* fields of an object *)
	| Arguments  of jsil_var                                                  (** Arguments of the current function *)
	| Seal       of jsil_expr                                                (** Seals the object *)
	| MetaData   of jsil_var * jsil_expr                                     (** Reads the metadata and assigns it to the first var *)

(** {b JSIL Commands}. JSIL commands incorporate basic commands as well as commands that
    affect control flow, which are goto statements, function calls, and PHI-nodes, which
    offer direct support for SSA. *)
type jsil_cmd =
	| Basic          of jsil_basic_cmd                                     (** JSIL basic commands *)
	| Goto           of int                                                (** Unconditional goto *)
	| GuardedGoto    of jsil_expr * int * int                              (** Conditional goto *)
	| Call           of jsil_var * jsil_expr * jsil_expr list * int option (** Classical procedure call *)
	| Apply          of jsil_var * jsil_expr list * int option             (** Application-style procedure call *)
	| PhiAssignment  of jsil_var * (jsil_expr array)                       (** PHI assignment *)
	| PsiAssignment  of jsil_var * (jsil_expr array)

(** {2 Syntax of JSIL Logic} *)

(** {b JSIL logic variables}. JSIL logic variables are internally represented as strings. *)
type jsil_logic_var = string [@@deriving show]

(** {b JSIL logic expressions}. *)
type jsil_logic_expr =
	| LLit      of Literal.t                                   (** JSIL literals ({!type:Literal.t}) *)
	| LVar      of jsil_logic_var                              (** JSIL logic variables ({!type:jsil_logic_var}) *)
	| ALoc      of string                                      (** Abstract locations *)
	| PVar      of jsil_var                                    (** JSIL program variables *)
	| LBinOp    of jsil_logic_expr * BinOp.t * jsil_logic_expr (** Binary operators ({!type:BinOp.t}) *)
	| LUnOp     of UnOp.t * jsil_logic_expr                    (** Unary operators ({!type:UnOp.t}) *)
	| LLstNth   of jsil_logic_expr * jsil_logic_expr           (** Nth element of a list *)
	| LStrNth   of jsil_logic_expr * jsil_logic_expr           (** Nth element of a string *)
	| LEList    of jsil_logic_expr list                        (** Lists of logical expressions *)
	| LESet     of jsil_logic_expr list                        (** Sets of logical expressions *)
	| LSetUnion of jsil_logic_expr list                        (** Unions *)
	| LSetInter of jsil_logic_expr list                        (** Intersections *)
	| LNone                                                    (** Empty field value *)
	[@@deriving show]

(** {b JSIL logic assertions}. *)
type jsil_logic_assertion =
	| LTrue                                                                              (** Logical true *)
	| LFalse                                                                             (** Logical false *)
	| LNot         of jsil_logic_assertion                                               (** Logical negation *)
	| LAnd         of jsil_logic_assertion * jsil_logic_assertion                        (** Logical conjunction *)
	| LOr          of jsil_logic_assertion * jsil_logic_assertion                        (** Logical disjunction *)
	| LEmp                                                                               (** Empty heap *)
	| LStar			   of jsil_logic_assertion * jsil_logic_assertion                        (** Separating conjunction *)
	| LPointsTo	   of jsil_logic_expr * jsil_logic_expr * (Permission.t * jsil_logic_expr) (** Heap cell assertion *)
	| LMetaData    of jsil_logic_expr * jsil_logic_expr                                  (** MetaData *)
	| LExtensible  of jsil_logic_expr * Extensibility.t                                  (** Extensibility *)
	| LPred			   of string * (jsil_logic_expr list)                                    (** Predicates *)
	| LForAll      of (jsil_var * Type.t) list * jsil_logic_assertion                    (** Forall *)
	| LTypes       of (jsil_logic_expr * Type.t) list                                    (** Typing assertion *)
	| LEmptyFields of jsil_logic_expr * jsil_logic_expr                                  (** emptyFields assertion *)
	| LEq          of jsil_logic_expr * jsil_logic_expr                                  (** Expression equality *)
	| LLess			   of jsil_logic_expr * jsil_logic_expr                                  (** Expression less-than for numbers *)
	| LLessEq		   of jsil_logic_expr * jsil_logic_expr                                  (** Expression less-than-or-equal for numbers *)
	| LStrLess	   of jsil_logic_expr * jsil_logic_expr                                  (** Expression less-than for strings *)
	| LSetMem  	   of jsil_logic_expr * jsil_logic_expr                                  (** Set membership *)
	| LSetSub      of jsil_logic_expr * jsil_logic_expr                                  (** Set subsetness *)


(** {b JSIL logic predicate}. *)
type jsil_logic_predicate = {
	name        : string;                                        (** Name of the predicate  *)
	num_params  : int;                                           (** Number of parameters   *)
	params      : (jsil_logic_expr * Type.t option) list;        (** Actual parameters      *)
  definitions : ((string option) * jsil_logic_assertion) list; (** Predicate definitions  *)
  previously_normalised_pred : bool                            (** If the predicate has been previously normalised *)
}

(** Creates/populates a Hashtbl from the predicate list pred_defs *)
let pred_def_tbl_from_list pred_defs =
	let pred_def_tbl = Hashtbl.create small_tbl_size in
	List.iter
		(fun pred_def -> Hashtbl.add pred_def_tbl pred_def.name pred_def)
		pred_defs;
	pred_def_tbl

(** {b Return flags for JSIL specifications}. *)
type jsil_return_flag =
	| Normal (** Normal return *)
	| Error  (** Error return *)

(** {b Single JSIL specifications}. *)
type jsil_single_spec = {
	pre      : jsil_logic_assertion;      (** Precondition *)
	post     : jsil_logic_assertion list; (** Postcondition *)
	ret_flag : jsil_return_flag           (** Return flag ({!type:jsil_return_flag}) *)
}

(** Keeps track of whether the current file is a previously normalised file **)
let previously_normalised = ref false;

(** {b Full JSIL specifications}. *)
type jsil_spec = {
	spec_name     : string;                (** Procedure/spec name *)
	spec_params   : jsil_var list;         (** Procedure/spec parameters *)
  proc_specs    : jsil_single_spec list; (** List of single specifications *)
  previously_normalised : bool           (** If the spec is already normalised *)
}

(**/**)
(** Creates a JSIL specification given it's components *)
let create_single_spec pre post flag =
	{
		pre      = pre;
		post     = post;
		ret_flag = flag
	}

let create_jsil_spec name params specs normalised =
	{
		spec_name   = name;
		spec_params = params;
    proc_specs  = specs;
    previously_normalised = normalised
	}
(**/**)

(** {b JSIL logic commands}. *)
type jsil_logic_command =
	| Fold             of jsil_logic_assertion                                                          (** Recursive fold *)
	| Unfold           of jsil_logic_assertion * ((string * ((string * jsil_logic_expr) list)) option)  (** Single unfold *)
	| ApplyLem		     of string * (jsil_logic_expr list)                                               (** Apply lemma *)
	| RecUnfold        of string                                                                        (** Recursive unfold of everything *)
	| LogicIf          of jsil_logic_expr * (jsil_logic_command list) * (jsil_logic_command list)       (** If-then-else *)
	| Macro            of string * (jsil_logic_expr list)                                               (** Macro *)
	| Assert           of jsil_logic_assertion                                                          (** Assert *)

(** {b JSIL lemmas}. *)
type jsil_lemma = {
	lemma_name    : string; (* Name of the lemma *)
	lemma_spec    : jsil_spec; (* The lemma spec *)
  lemma_proof   : (jsil_logic_command list) option;  (** (Optional) Proof body *)
  lemma_variant : jsil_expr option (* The paramater to treat as the variant. Will trigger termination checks *)
}

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
	| LBasic          of jsil_basic_cmd
	| LGoto           of string
	| LGuardedGoto    of jsil_expr * string * string
	| LCall           of jsil_var  * jsil_expr * jsil_expr list * string option
	| LApply          of jsil_var  * jsil_expr list * string option
	| LPhiAssignment  of jsil_var  * (jsil_expr array)
	| LPsiAssignment  of jsil_var  * (jsil_expr array)

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
	(* Lemmas *)
	lemmas : (string, jsil_lemma) Hashtbl.t;
	(* Predicates = Name : String --> Definition *)
	predicates : (string, jsil_logic_predicate) Hashtbl.t;
	(* Specs = Name : String --> Spec *)
	onlyspecs : (string, jsil_spec) Hashtbl.t;
	(* JSIL extended procedures = Name : String --> Procedure *)
	procedures : (string, jsil_ext_procedure) Hashtbl.t;
	(* List of JSIL procedure names in order.*)
	procedure_names : (string list);
}

(* Normalised predicate *)
type normalised_predicate = {
  name         : string;
  num_params   : int;
  params       : jsil_var list;
  definitions  : ((string option) * jsil_logic_assertion) list;
  is_recursive : bool
}

type lemma_table         = (string, jsil_lemma) Hashtbl.t
type which_predecessor   = (string * int * int, int) Hashtbl.t


(*************************************)
(** JSIL Logic Macros               **)
(*************************************)

(* Associates a string with a jsil_logic_macro *)
let macro_table : (string, jsil_logic_macro) Hashtbl.t = Hashtbl.create 511


(*************************************)
(** JSIL Heaps                      **)
(*************************************)

(* a heap is a hash-table mapping strings to a new type 'a *)
module Heap = Hashtbl.Make(
	struct
		type t = string           (* keys are of type string *)
		let equal = (=)           (* use standard equality operator *)
		let hash = Hashtbl.hash   (* and default hash function *)
	end)
 
type jsil_heap = (((Permission.t * Literal.t) Heap.t) * MetaData.t * Extensibility.t) Heap.t


(* creates a heap of the appropiate size *)
let make_initial_heap is_big =
	let size = if (is_big) then big_tbl_size else small_tbl_size in (* 2 options for size of the heap *)
	let heap = Heap.create size in
	heap

(** Basic functions **)

(* Retrieves the return variable of the given procedure w.r.t. the given return flag *)
let proc_get_ret_var proc ret_flag =
	let ret_var =
		match ret_flag with
		| Normal -> proc.ret_var
		| Error -> proc.error_var in
	match ret_var with
	| Some ret_var -> ret_var
	| None -> raise (Failure "proc_get_ret_var: fatal error") (* no variable exists *)

(* Retrieves the procedure with the given name from the given program *)
let get_proc prog proc_name =
	try
		Hashtbl.find prog proc_name
	with _ ->
		raise (Failure "get_proc: fatal error")

let get_proc_args proc = proc.proc_params (* shorthand *)

(* Retrieves the given i'th command of the given procedure *)
let get_proc_cmd proc i =
	proc.proc_body.(i)

(* SETS *)

(*** Defining the real types and comparators of each of the set types ***)
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

module MySubstitution =
	struct
		type t = (string, jsil_logic_expr) Hashtbl.t
		let compare = Pervasives.compare
	end

module MyExpr =
	struct
		type t = jsil_expr
		let compare = Pervasives.compare
	end

module MyLExpr =
	struct
		type t = jsil_logic_expr
		let compare = Pervasives.compare
	end

module MyFieldValueList =
	struct
		type t = jsil_logic_expr * (Permission.t * jsil_logic_expr)
		let compare = Pervasives.compare
	end

module MyBool =
	struct
		type t = bool
		let compare = Pervasives.compare
	end

(*** Creating sets for each of our types ***)
module SI = Set.Make(MyInt)
module SB = Set.Make(MyBool)
module SN = Set.Make(MyNumber)
module SA = Set.Make(MyAssertion)

module SSS = Set.Make(MySubstitution)

module SExpr = Set.Make(MyExpr)
module SLExpr = Set.Make(MyLExpr)

module SFV = Set.Make(MyFieldValueList)


(*******************************************************)
(*******************************************************)
(* A substitution type                                 *)
(*******************************************************)
(*******************************************************)
type substitution      = ((string, jsil_logic_expr) Hashtbl.t)
type substitution_list = ((string * jsil_logic_expr) list) 

let init_substitution (vars : string list) : substitution =
	let new_subst = Hashtbl.create big_tbl_size in
	List.iter
		(fun var -> Hashtbl.replace new_subst var (LVar var))
		vars;
	new_subst

let init_substitution2 vars les =
	let subst = Hashtbl.create big_tbl_size in

	let rec loop vars les =
		match vars, les with
		| [], _
		| _, [] -> ()
		| var :: rest_vars, le :: rest_les ->
			Hashtbl.replace subst var le; loop rest_vars rest_les in

	loop vars les;
	subst

let init_substitution3 vars_les =
	let subst = Hashtbl.create big_tbl_size in

	let rec loop vars_les =
		match vars_les with
		| [] -> ()
		| (var, le) :: rest ->
			Hashtbl.replace subst var le; loop rest in

	loop vars_les;
	subst

let substitution_range (subst : substitution) : jsil_logic_expr list = 
	Hashtbl.fold (fun x le ac -> le :: ac) subst [] 

(* creates an expression of equality from the substitution table *)
let assertions_of_substitution (subst : substitution) =
	Hashtbl.fold
    (fun v le ac -> (LEq (LVar v, le)) :: ac)  (* the fold function - forms an expression from the variables *)
		subst                                      (* the substituion table *)
		[]                                         (* base element *)

let copy_substitution (subst : substitution) : substitution = Hashtbl.copy subst

let extend_substitution (subst : substitution) (vars : string list) (les : jsil_logic_expr list) : unit =
	List.iter2 (fun v le -> Hashtbl.replace subst v le) vars les

let extend_subst_with_subst (subst : substitution) (subst_ext : substitution) : unit =
	Hashtbl.iter (fun v le -> Hashtbl.replace subst v le) subst_ext
	
(* JS2JSIL *)
let for_verification = ref false
