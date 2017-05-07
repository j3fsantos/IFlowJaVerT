%{
open JSIL_Syntax
open JSIL_Syntax_Checks
open JS_Logic_Syntax
(* Tables where we collect the predicates and the procedures as we parse them. *)
let predicate_table : (string, jsil_logic_predicate) Hashtbl.t = Hashtbl.create 511
let procedure_table : (string, jsil_ext_procedure) Hashtbl.t = Hashtbl.create 511
let only_spec_table : (string, jsil_spec) Hashtbl.t = Hashtbl.create 511
let procedure_names  : (string list) ref = ref []
let copy_and_clear_globals () = 
	let pred' = Hashtbl.copy predicate_table in
	let ospc' = Hashtbl.copy only_spec_table in
	let proc' = Hashtbl.copy procedure_table in
	let proc_names = !procedure_names in
	Hashtbl.clear predicate_table;
	Hashtbl.clear procedure_table;
	Hashtbl.clear only_spec_table;
	procedure_names = ref [];
	(pred' , ospc', proc', proc_names)
%}

(***** Token definitions *****)
(*  JS Logic Literals *)
%token SCOPE
%token THIS
%token FUNOBJ
%token CLOSURE
%token SCSCOPE 
%token OCHAINS
(* Type literals *)
%token UNDEFTYPELIT
%token NULLTYPELIT
%token EMPTYTYPELIT
%token NONETYPELIT
%token BOOLTYPELIT
%token NUMTYPELIT
%token STRTYPELIT
%token OBJTYPELIT
%token LISTTYPELIT
%token TYPETYPELIT
%token SETTYPELIT
(* Constants *)
%token MIN_FLOAT
%token MAX_FLOAT
%token RANDOM
%token E
%token LN10
%token LN2
%token LOG2E
%token LOG10E
%token PI
%token SQRT1_2
%token SQRT2
%token UTCTIME
%token LOCALTIME
(* Literals *)
%token UNDEFINED
%token NULL
%token EMPTY
%token TRUE
%token FALSE
%token <float> FLOAT
%token NAN
%token INFINITY
%token <string> STRING
%token <string> LOC
%token LSTNIL
%token LSTOPEN
%token LSTCLOSE
(* Variables *)
%token <string> VAR
(* Binary operators *)
%token EQUAL
%token LESSTHAN
%token LESSTHANEQUAL
%token LESSTHANSTRING
%token PLUS
%token MINUS
%token TIMES
%token DIV
%token MOD
%token AND
%token OR
%token BITWISEAND
%token BITWISEOR
%token BITWISEXOR
%token LEFTSHIFT
%token SIGNEDRIGHTSHIFT
%token UNSIGNEDRIGHTSHIFT
%token M_ATAN2
%token M_POW
%token LSTCONS
%token LSTCAT
%token STRCAT
(* Unary operators *)
(* Unary minus uses the same token as binary minus: MINUS *)
%token NOT
%token BITWISENOT
%token M_ABS
%token M_ACOS
%token M_ASIN
%token M_ATAN
%token M_CEIL
%token M_COS
%token M_EXP
%token M_FLOOR
%token M_LOG
%token M_ROUND
%token M_SGN
%token M_SIN
%token M_SQRT
%token M_TAN
%token ISPRIMITIVE
%token TOSTRING
%token TOINT
%token TOUINT16
%token TOINT32
%token TOUINT32
%token TONUMBER
%token CAR
%token CDR
%token LSTLEN
%token STRLEN
(* Expression keywords *)
%token TYPEOF
%token ASSUME
%token ASSERT
%token RNUMSYM
%token RSTRSYM
%token LSTNTH
%token STRNTH
(* Command keywords  *)
%token SKIP
%token DEFEQ
%token NEW
%token DELETE
%token DELETEOBJ
%token HASFIELD
%token GETFIELDS
%token ARGUMENTS
%token GOTO
%token WITH
%token APPLY
%token PHI
%token PSI
(* Logic variables *)
%token <string> LVAR
(* Logical expressions *)
%token LNONE
(* Logic assertions *)
%token OASSERT
%token CASSERT
%token LAND
%token LOR
%token LNOT
%token LTRUE
%token LFALSE
%token LEQUAL
%token LLESSTHAN
%token LLESSTHANEQUAL
%token LLESSTHANSTRING
%token LARROW
%token LEMP
%token EMPTYFIELDS
(*%token LEXISTS *)
%token LFORALL 
%token LTYPES
(* Logic predicates *)
%token PRED
(* Logic commands *)
%token OLCMD
%token CLCMD
%token OOLCMD
%token CCLCMD
%token FOLD
%token UNFOLD
%token RECUNFOLD
%token CALLSPEC
%token LIF
%token LTHEN
%token LELSE
(* Procedure specification keywords *)
%token ONLY
%token SPEC
%token NORMAL
%token ERROR
(* JS only spec specifics *)
%token JSOS
%token JSOSPRE
%token JSOSPOST
%token JSOSOUT
(* Procedure definition keywords *)
%token PROC
%token RET
%token ERR
(* Others *)
%token IMPORT
%token MACRO
(* Separators *)
%token DOT
%token COMMA
%token COLON
%token SCOLON
(*%token DOT*)
%token LBRACE
%token RBRACE
%token LBRACKET
%token RBRACKET
%token CLBRACKET
%token CRBRACKET
(* SETS *)
%token EMPTYSET
%token SETUNION
%token SETINTER
%token SETDIFF
%token SETMEM
%token SETSUB
%token LSETMEM
%token LSETSUB
%token SETOPEN
%token SETCLOSE
(* EOF *)
%token EOF
(***** Precedence of operators *****)
(* The later an operator is listed, the higher precedence it is given. *)
(* Logic operators have lower precedence *)
(*%nonassoc DOT*)
%left LOR
%left LAND
%left separating_conjunction
%right LNOT
%nonassoc LEQUAL LLESSTHAN LLESSTHANEQUAL LLESSTHANSTRING LARROW
(* Program operators have higher precedence.*)
(* Based on JavaScript:
   https://developer.mozilla.org/en/docs/Web/JavaScript/Reference/Operators/Operator_Precedence *)
%left OR
%left AND
%left BITWISEOR
%left BITWISEXOR
%left BITWISEAND
%left EQUAL
%nonassoc LESSTHAN LESSTHANSTRING LESSTHANEQUAL 
%left LEFTSHIFT SIGNEDRIGHTSHIFT UNSIGNEDRIGHTSHIFT
%left PLUS MINUS
%left TIMES DIV MOD M_POW
%right NOT BITWISENOT unary_minus
%left M_ATAN2 LSTCAT STRCAT
%right M_ABS M_ACOS M_ASIN M_ATAN M_CEIL M_COS M_EXP M_FLOOR M_LOG M_ROUND M_SGN M_SIN M_SQRT M_TAN
  ISPRIMITIVE TOSTRING TOINT TOUINT16 TOINT32 TOUINT32 TONUMBER CAR CDR LSTLEN STRLEN LSTCONS

%nonassoc FLOAT

(***** Types and entry points *****)
%type <JSIL_Syntax.jsil_ext_program> main_target
%type <string list> param_list_FC_target
%type <JSIL_Syntax.jsil_logic_predicate list * JSIL_Syntax.jsil_spec list> pred_spec_target
%type <JS_Logic_Syntax.js_logic_predicate> js_pred_target
%type <JSIL_Syntax.jsil_logic_assertion> top_level_assertion_target
%type <JS_Logic_Syntax.js_logic_assertion> top_level_js_assertion_target
%type <unit> js_only_spec_target
%start main_target
%start param_list_FC_target
%start pred_spec_target
%start top_level_assertion_target
%start top_level_js_assertion_target
%start js_pred_target
%start js_only_spec_target
%%

(********* JSIL *********)

main_target:
	| imports = import_target; declaration_target; EOF
		{  let (pred, ospc, proc, proc_names) = copy_and_clear_globals () in
			{ imports; predicates = pred; onlyspecs = ospc; procedures = proc; procedure_names = List.rev proc_names } }
	| declaration_target; EOF
		{   let (pred, ospc, proc, proc_names) = copy_and_clear_globals () in
			{ imports = []; predicates = pred; onlyspecs = ospc; procedures = proc; procedure_names = List.rev proc_names } }
;

declaration_target:
	| declaration_target; pred_target
	| pred_target
	| declaration_target; proc_target
	| proc_target 
	| declaration_target; macro_target
	| macro_target 
	| declaration_target; only_spec_target
	| only_spec_target 
	{ }
;

import_target:
  IMPORT; imports = separated_nonempty_list(COMMA, VAR); SCOLON { imports }
;

proc_target:
(* [spec;] proc xpto (x, y) { cmd_list } with { ret: x, i; [err: x, j] }; *)
  proc_head = proc_head_target;
		CLBRACKET; cmd_list = cmd_list_target; CRBRACKET;
	WITH;
		CLBRACKET; ctx_ret = option(ctx_target_ret); ctx_err = option(ctx_target_err); CRBRACKET; SCOLON
	{
		(* Printf.printf "Parsing Procedure.\n"; *)
		let (lproc_name, lproc_params, spec) = proc_head in
		let lret_var, lret_label =
		(match ctx_ret with
			| None -> None, None
			| Some (rv, ri) -> Some rv, Some ri) in
		let lerror_var, lerror_label =
			(match ctx_err with
			| None -> None, None
			| Some (ev, ei) -> Some ev, Some ei) in
		(* Replace keywords "ret" and "err" from the postcondition with the correspondig program variables *)
		let lspec = replace_spec_keywords spec lret_var lerror_var in
		let proc = {
			lproc_name;
			lproc_body = Array.of_list cmd_list;
			lproc_params;
			lret_label;
			lret_var;
			lerror_label;
			lerror_var;
			lspec;
		} in
		(* TODO: Warn if conflicting names? *)
		procedure_names :=  lproc_name :: (!procedure_names);
		Hashtbl.replace procedure_table lproc_name proc;
	}
;

param_list_FC_target:
	param_list = separated_list(COMMA, VAR); EOF
	{ param_list };

proc_head_target:
	spec = option(spec_target);
	PROC; proc_name = VAR; LBRACE; param_list = separated_list(COMMA, VAR); RBRACE
	{ (* TODO: Check pvars statically in the logic commands? *)
		enter_procedure ();
		validate_proc_signature spec proc_name param_list;
		(proc_name, param_list, spec)
	}
;

ctx_target_ret:
(* ret: x, i; *)
	RET; COLON; ret_v=VAR; COMMA; i=VAR; SCOLON
	{
		(* Printf.printf "Parsing return context.\n"; *)
		ret_v, i
	}
;

ctx_target_err:
(* err: x, j *)
	ERR; COLON; err_v=VAR; COMMA; j=VAR; SCOLON
	{
		(* Printf.printf "Parsing error context.\n"; *)
		err_v, j
	}
;

cmd_list_target:
	cmd_list = separated_nonempty_list(SCOLON, cmd_with_label_and_logic)
	{
		List.map
			(fun (invariant, pre_logic_cmds, post_logic_cmds, lab, cmd) ->
				({ line_offset = None; invariant; pre_logic_cmds; post_logic_cmds }, lab, cmd))
			cmd_list
	}
;

cmd_with_label_and_logic:
	| pre = option(spec_line); pre_logic_cmds = option(pre_logic_cmd_target);
			cmd = cmd_target; post_logic_cmds = option(post_logic_cmd_target)
		{
			let pre_logic_cmds =
				match pre_logic_cmds with
				| None -> []
				| Some pre_logic_cmds -> pre_logic_cmds in
			let post_logic_cmds =
				match post_logic_cmds with
				| None -> []
				| Some post_logic_cmds -> post_logic_cmds  in
			(pre, pre_logic_cmds, post_logic_cmds, None, cmd)
		}
	| pre = option(spec_line); pre_logic_cmds = option(pre_logic_cmd_target);
		lab = VAR; COLON; cmd = cmd_target; post_logic_cmds = option(post_logic_cmd_target)
		{
			let pre_logic_cmds =
				match pre_logic_cmds with
				| None -> []
				| Some pre_logic_cmds -> pre_logic_cmds in
			let post_logic_cmds =
				match post_logic_cmds with
				| None -> []
				| Some post_logic_cmds -> post_logic_cmds  in
			(pre, pre_logic_cmds, post_logic_cmds, Some lab, cmd)
		}
;

cmd_target:
(*** Basic commands ***)
(* skip *)
	| SKIP
		{ SLBasic (SSkip) }
(* x := e *)
	| v=VAR; DEFEQ; e=expr_target
		{ SLBasic (SAssignment (v, e)) }
(* x := new() *)
	| v=VAR; DEFEQ; NEW; LBRACE; RBRACE
		{ SLBasic (SNew v) }
(* x := [e1, e2] *)
	| v=VAR; DEFEQ; LBRACKET; e1=expr_target; COMMA; e2=expr_target; RBRACKET
		{ SLBasic (SLookup (v, e1, e2)) }
(* [e1, e2] := e3 *)
	| LBRACKET; e1=expr_target; COMMA; e2=expr_target; RBRACKET; DEFEQ; e3=expr_target
		{ SLBasic (SMutation (e1, e2, e3)) }
(* delete(e1, e2) *)
	| DELETE; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
		{ SLBasic (SDelete (e1, e2)) }
(* deleteObject(e1) *)
	| DELETEOBJ; LBRACE; e1=expr_target; RBRACE
		{ SLBasic (SDeleteObj (e1)) }
(* x := hasField(e1, e2) *)
	| v=VAR; DEFEQ; HASFIELD; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
		{ SLBasic (SHasField (v, e1, e2)) }
(* x := getFields (e1) *)
	| v = VAR; DEFEQ; GETFIELDS; LBRACE; e=expr_target; RBRACE
		{ SLBasic (SGetFields (v, e)) }
(* x := args *)
	| v = VAR; DEFEQ; ARGUMENTS
	  { SLBasic (SArguments v) }
(*** Other commands ***)
(* goto i *)
	| GOTO; i=VAR
		{ SLGoto i }
(* goto [e] i j *)
	| GOTO LBRACKET; e=expr_target; RBRACKET; i=VAR; j=VAR
		{ SLGuardedGoto (e, i, j) }
(* x := e(e1, ..., en) with j *)
	| v=VAR; DEFEQ; e=expr_target;
	  LBRACE; es=separated_list(COMMA, expr_target); RBRACE; oi = option(call_with_target)
		{ SLCall (v, e, es, oi) }
(* x := apply (e1, ..., en) with j *)
	| v=VAR; DEFEQ; APPLY;
	  LBRACE; es=separated_list(COMMA, expr_target); RBRACE; oi = option(call_with_target)
		{ SLApply (v, es, oi) }
(* x := PHI(e1, e2, ... en); *)
  | v=VAR; DEFEQ; PHI; LBRACE; es = separated_list(COMMA, expr_target); RBRACE
	  { SLPhiAssignment (v, Array.of_list es) }
(* x := PSI(e1, e2, ... en); *)
  | v=VAR; DEFEQ; PSI; LBRACE; es = separated_list(COMMA, expr_target); RBRACE
	  { SLPsiAssignment (v, Array.of_list es) }
;

call_with_target:
	WITH; i=VAR { i }
;

expr_target:
(* literal *)
	| lit=lit_target { Literal lit }
(* var *)
	| v=VAR { Var v }
(* e binop e *)
	| e1=expr_target; bop=binop_target; e2=expr_target
		{ BinOp (e1, bop, e2) }
(* unop e *)
  | uop=unop_target; e=expr_target
		{ UnOp (uop, e) }
(* - e *)
(* Unary negation has the same precedence as logical not, not as binary negation. *)
	| MINUS; e=expr_target
		{ UnOp (UnaryMinus, e) } %prec unary_minus
(* typeOf *)
	| TYPEOF; LBRACE; e=expr_target; RBRACE
		{ TypeOf (e) }
(* asssume (e) *)
  | ASSUME; LBRACE; e=expr_target; RBRACE
	  { RAssume (e) }
(* assert (e) *)
  | ASSERT; LBRACE;  e=expr_target; RBRACE
	  { RAssert (e) }
(* make_symbol_number() *)
  | RNUMSYM; LBRACE;  RBRACE
	  { RNumSymb }
(* make_symbol_string() *)
  | RSTRSYM; LBRACE; RBRACE
	  { RStrSymb }
(* {{ e, ..., e }} *)
	| LSTOPEN; exprlist = separated_nonempty_list(COMMA, expr_target); LSTCLOSE
		{ EList exprlist }
(* -{- e, ..., e -}- *)
	| SETOPEN; exprlist = separated_list(COMMA, expr_target); SETCLOSE
		{ ESet (SExpr.elements (SExpr.of_list exprlist)) }
(* l-nth (list, n) *)
	| LSTNTH; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
		{ LstNth (e1, e2) }
(* s-nth (string, n) *)
	| STRNTH; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
		{ StrNth (e1, e2) }
(* Set union and intersection *)
	| SETUNION LBRACE; le = separated_list(COMMA, expr_target); RBRACE
	  { SetUnion (SExpr.elements (SExpr.of_list le)) }
	| SETINTER LBRACE; le = separated_list(COMMA, expr_target); RBRACE
	  { SetInter (SExpr.elements (SExpr.of_list le)) }
(* (e) *)
  | LBRACE; e=expr_target; RBRACE
		{ e }
;

(********* LOGIC *********)

pred_target:
(* pred name (arg1, ..., argn) : def1, ..., defn ; *)
	PRED; pred_head = pred_head_target; COLON;
	definitions = separated_nonempty_list(COMMA, assertion_target); SCOLON
  { (* Add the predicate to the collection *)
		let (name, num_params, params) = pred_head in
	  let pred = { name; num_params; params; definitions; } in
		Hashtbl.add predicate_table name pred;
    pred
	}
;


js_pred_target:
(* pred name (arg1, ..., argn) : def1, ..., defn ; *)
	PRED; pred_head = js_pred_head_target; COLON;
	definitions = separated_nonempty_list(COMMA, js_assertion_target); SCOLON
  { (* Add the predicate to the collection *)
		let (name, num_params, params) = pred_head in
	  let pred = { js_name = name; js_num_params = num_params; js_params = params; js_definitions = definitions } in
    pred
	}
;


pred_head_target:
  name = VAR; LBRACE; params = separated_list(COMMA, pred_param_target); RBRACE;
	{ (* Register the predicate declaration in the syntax checker *)
		let num_params = List.length params in
		register_predicate name num_params;
		enter_predicate params;
	  (name, num_params, params)
	}
;


js_pred_head_target:
  name = VAR; LBRACE; params = separated_list(COMMA, js_pred_param_target); RBRACE;
	{ (* Register the predicate declaration in the syntax checker *)
		let num_params = List.length params in
	  (name, num_params, params)
	}
;

pred_param_target:
(* Logic literal *)
	| lit = lit_target
	  { LLit lit }
(* None *)
	| LNONE
	  { LNone }
(* Program variable *)
	| v = VAR
	  { PVar v }
;


js_pred_param_target:
(* Logic literal *)
	| lit = lit_target
	  { JSLLit lit }
(* None *)
	| LNONE
	  { JSLNone }
(* Program variable *)
	| v = VAR
	  { JSPVar v }
;


pre_logic_cmd_target:
(* [* logic_cmds *] *)
	| OLCMD; logic_cmds = separated_list(SCOLON, logic_cmd_target); CLCMD
		{ logic_cmds }

post_logic_cmd_target:
(* [+ logic_cmds +] *)
	| OOLCMD; logic_cmds = separated_list(SCOLON, logic_cmd_target); CCLCMD
		{ logic_cmds }



(* TODO: Check that the assertions are only predicates, or deal with full assertions in the execution *)
logic_cmd_target:
(* fold x(e1, ..., en) *)
	| FOLD; assertion = assertion_target
	  { Fold (assertion) }
(* unfold x(e1, ..., en) *)
	| UNFOLD; assertion = assertion_target
	  { Unfold (assertion) }
(* unfold* x *)
	| RECUNFOLD; v = VAR
	  { RecUnfold v }
(* callspec spec_name(ret_var, args) *)
	| CALLSPEC; spec_name = VAR; LBRACE; params = separated_list(COMMA, lexpr_target); RBRACE; 
	  { 
	  	match params with 
	  	| (LVar ret_var) :: rest_params ->  CallSpec (spec_name, ret_var, rest_params) 
	  	| _ -> raise (Failure "DEATH: Parser: CALLSPEC ")
	 }
(* if(le) { lcmd* } else { lcmd* } *)
	| LIF; LBRACE; le=lexpr_target; RBRACE; LTHEN; CLBRACKET;
			then_lcmds = separated_list(SCOLON, logic_cmd_target);
			CRBRACKET; LELSE; CLBRACKET;
			else_lcmds = separated_list(SCOLON, logic_cmd_target);
			 CLBRACKET;
	  { LogicIf (le, then_lcmds, else_lcmds)}
(* if(e) { lcmd* } *)
	| LIF; LBRACE; le=lexpr_target; RBRACE; LTHEN; CLBRACKET;
			then_lcmds = separated_list(SCOLON, logic_cmd_target);
			CRBRACKET;
	  { LogicIf (le, then_lcmds, [])}
	| macro = macro_head_target;
		{ let (name, params) = macro in Macro (name, params) }
;

macro_target: 
	MACRO; head = macro_head_def_target; COLON; command = logic_cmd_target; SCOLON
  { let (name, params) = head in
		let macro = { mname = name; mparams = params; mdefinition = command } in 
		Hashtbl.add macro_table macro.mname macro } 

macro_head_def_target:
 | name = VAR; LBRACE; params = separated_list(COMMA, VAR); RBRACE
	 { (name, params) }

macro_head_target:
 | name = VAR; LBRACE; params = separated_list(COMMA, lexpr_target); RBRACE
	 { (name, params) }

only_spec_target:
(* only spec xpto (x, y) pre: assertion, post: assertion, flag: NORMAL|ERROR *)
	ONLY; SPEC; spec_head = spec_head_target;
	proc_specs = separated_nonempty_list(SCOLON, pre_post_target);
	{ let (spec_name, spec_params) = spec_head in
		let spec = { spec_name; spec_params; proc_specs } in
		Hashtbl.replace only_spec_table spec_name spec;
	}

js_only_spec_target:
(* js_only_spec xpto (x, y) pre: assertion, post: assertion, flag: NORMAL|ERROR *)
	JSOS; spec_head = spec_head_target;
	js_proc_specs = separated_nonempty_list(SCOLON, js_pre_post_target); EOF
	{
		let (js_spec_name, js_spec_params) = spec_head in
		let js_spec = { js_spec_name; js_spec_params; js_proc_specs } in
		Hashtbl.replace js_only_spec_table js_spec_name js_spec
	}
	
js_pre_post_target:
(* pre: ... post: ... outcome: ... *)
	JSOSPRE; OASSERT; js_pre = js_assertion_target; CASSERT;
	JSOSPOST; OASSERT; js_post = js_assertion_target; CASSERT;
	JSOSOUT; js_ret_flag = outcome_target;
	{ { js_pre; js_post; js_ret_flag } }
;

outcome_target:
	| NORMAL { Normal }
	| ERROR  { Error  }

spec_target:
(* spec xpto (x, y) pre: assertion, post: assertion, flag: NORMAL|ERROR *)
	SPEC; spec_head = spec_head_target;
	proc_specs = separated_nonempty_list(SCOLON, pre_post_target);
	{ let (spec_name, spec_params) = spec_head in
		{ spec_name; spec_params; proc_specs }
	}
;

spec_head_target:
  spec_name = VAR; LBRACE; spec_params = separated_list(COMMA, VAR); RBRACE
	{ enter_specs spec_params;
		(spec_name, spec_params)
	}
;

pre_post_target:
(* [[ .... ]] [[ .... ]] Normal *)
	| pre = spec_line; post = spec_line; NORMAL
		{ { pre; post; ret_flag = Normal } }
(* [[ .... ]] [[ .... ]] Error *)
	| pre = spec_line; post = spec_line; ERROR
		{ { pre; post; ret_flag = Error } }
;

spec_line:
  OASSERT; assertion = assertion_target; CASSERT { assertion }
;

top_level_assertion_target:
	a = assertion_target; EOF { a }

assertion_target:
(* P /\ Q *)
	| left_ass=assertion_target; LAND; right_ass=assertion_target
		{ LAnd (left_ass, right_ass) }
(* P \/ Q *)
	| left_ass=assertion_target; LOR; right_ass=assertion_target
		{ LOr (left_ass, right_ass) }
(* ! Q *)
	| LNOT; ass=assertion_target
		{ LNot (ass) }
(* true *)
  | LTRUE
		{ LTrue }
(* false *)
  | LFALSE
		{ LFalse }
(* E == E *)
	| left_expr=lexpr_target; LEQUAL; right_expr=lexpr_target
		{ LEq (left_expr, right_expr) }
(* E <# E *)
	| left_expr=lexpr_target; LLESSTHAN; right_expr=lexpr_target
		{ LLess (left_expr, right_expr) }
(* E <=# E *)
	| left_expr=lexpr_target; LLESSTHANEQUAL; right_expr=lexpr_target
		{ LLessEq (left_expr, right_expr) }
(* E <s# E *)
	| left_expr=lexpr_target; LLESSTHANSTRING; right_expr=lexpr_target
		{ LStrLess (left_expr, right_expr) }
(* P * Q *)
(* The precedence of the separating conjunction is not the same as the arithmetic product *)
	| left_ass=assertion_target; TIMES; right_ass=assertion_target
		{ LStar (left_ass, right_ass) } %prec separating_conjunction
(* (E, E) -> E *)
	| LBRACE; obj_expr=lexpr_target; COMMA; prop_expr=lexpr_target; RBRACE; LARROW; val_expr=lexpr_target
		{ LPointsTo (obj_expr, prop_expr, val_expr) }
(* emp *)
	| LEMP;
		{ LEmp }
(* exists X, Y, Z . P
	| LEXISTS; vars = separated_nonempty_list(COMMA, LVAR); DOT; ass = assertion_target
		{ LExists (vars, ass) } *)
(* forall X, Y, Z . P *)
	| LFORALL; vars = separated_nonempty_list(COMMA, lvar_type_target); DOT; ass = assertion_target
		{ LForAll (vars, ass) }
(* x(e1, ..., en) *)
	| name = VAR; LBRACE; params = separated_list(COMMA, lexpr_target); RBRACE
	  { (* validate_pred_assertion (name, params); *)
			LPred (name, params)
		}
(* types (type_pairs) *)
  | LTYPES; LBRACE; type_pairs = separated_list(COMMA, type_env_pair_target); RBRACE
    { LTypes type_pairs }
(* empty_fields (le : lit1, lit2, lit3, ...) *)
	| EMPTYFIELDS; LBRACE; le=lexpr_target; COLON; fields=separated_list(COMMA, lexpr_target); RBRACE
		{ LEmptyFields (le, fields) }
(* E --e-- E *)
	| left_expr=lexpr_target; LSETMEM; right_expr=lexpr_target
		{ LSetMem (left_expr, right_expr) }
(* E --s-- E *)
	| left_expr=lexpr_target; LSETSUB; right_expr=lexpr_target
		{ LSetSub (left_expr, right_expr) }
(* (P) *)
  | LBRACE; ass=assertion_target; RBRACE
	  { ass }
;

lvar_type_target:
	| lvar = just_logic_variable_target; COLON; the_type = type_target
	  { (lvar, the_type) }

type_env_pair_target:
  | lvar = logic_variable_target; COLON; the_type=type_target
    { (lvar, the_type) }
  | pvar = program_variable_target; COLON; the_type=type_target
    { (pvar, the_type) }
;

lexpr_target:
(* Logic literal *)
	| lit = lit_target
	  { LLit lit }
(* None *)
	| LNONE
	  { LNone }
(* Logic variable *)
	| lvar = logic_variable_target
	  { lvar }
(* Abstract locations are computed on normalisation *)
(* Program variable (including the special variable "ret") *)
	| pvar = program_variable_target
	  { pvar }
(* e binop e *)
	| e1=lexpr_target; bop=binop_target; e2=lexpr_target
		{ LBinOp (e1, bop, e2) }
(* unop e *)
  | uop=unop_target; e=lexpr_target
		{ LUnOp (uop, e) }
(* - e *)
(* Unary negation has the same precedence as logical not, not as binary negation. *)
	| MINUS; e=lexpr_target
		{ LUnOp (UnaryMinus, e) } %prec unary_minus
(* typeOf *)
	| TYPEOF; LBRACE; e=lexpr_target; RBRACE
		{ LTypeOf (e) }
(* {{ e, ..., e }} *)
	| LSTOPEN; exprlist = separated_nonempty_list(COMMA, lexpr_target); LSTCLOSE
		{ LEList exprlist }
(* -{- e, ..., e -}- *)
	| SETOPEN; exprlist = separated_list(COMMA, lexpr_target); SETCLOSE
		{ LESet (SLExpr.elements (SLExpr.of_list exprlist)) }
(* l-nth(e1, e2) *)
	| LSTNTH; LBRACE; e1=lexpr_target; COMMA; e2=lexpr_target; RBRACE
		{ LLstNth (e1, e2) }
(* s-nth(e1, e2) *)
	| STRNTH; LBRACE; e1=lexpr_target; COMMA; e2=lexpr_target; RBRACE
		{ LStrNth (e1, e2) }
	| SETUNION LBRACE; le = separated_list(COMMA, lexpr_target); RBRACE
	  { LSetUnion (SLExpr.elements (SLExpr.of_list le)) }
	| SETINTER LBRACE; le = separated_list(COMMA, lexpr_target); RBRACE
	  { LSetInter (SLExpr.elements (SLExpr.of_list le)) }
(* (e) *)
  | LBRACE; e=lexpr_target; RBRACE
	  { e }
;

logic_variable_target:
  v = LVAR
	{ validate_lvar v; LVar v }
;

just_logic_variable_target:
  v = LVAR
	{ validate_lvar v; v }

program_variable_target:
  | v = VAR
	  { let _ = validate_pvar v in PVar v }
	| RET
	  { let _ = validate_pvar "ret" in PVar "ret" }
	| ERR
	  { let _ = validate_pvar "err" in PVar "err" }
;

(********* PREDS and SPECS only *********)

pred_spec_target: preds = separated_list(AND, pred_target); specs = separated_list(AND, spec_target); EOF
  { preds, specs }

(********* COMMON *********)

lit_target:
	| UNDEFINED                 { Undefined }
	| NULL                      { Null }
	| EMPTY                     { Empty }
	| constant_target           { Constant $1 }
	| TRUE                      { Bool true }
	| FALSE                     { Bool false }
	| FLOAT                     { Num $1 }
	| NAN                       { Num nan }
	| INFINITY                  { Num infinity }
	| STRING                    { String $1 }
	| LOC                       { Loc $1 }
	| type_target               { Type $1 }
	| LSTNIL                    { LList [] }
	| LSTOPEN LSTCLOSE          { LList [] }
;

%inline binop_target:
	| EQUAL              { Equal }
	| LESSTHAN           { LessThan }
	| LESSTHANEQUAL      { LessThanEqual }
	| LESSTHANSTRING     { LessThanString }
	| PLUS               { Plus }
	| MINUS              { Minus }
	| TIMES              { Times }
	| DIV                { Div }
	| MOD                { Mod }
	| AND                { And }
	| OR                 { Or }
	| BITWISEAND         { BitwiseAnd }
	| BITWISEOR          { BitwiseOr}
	| BITWISEXOR         { BitwiseXor }
	| LEFTSHIFT          { LeftShift }
	| SIGNEDRIGHTSHIFT   { SignedRightShift }
	| UNSIGNEDRIGHTSHIFT { UnsignedRightShift }
	| M_ATAN2            { M_atan2 }
	| M_POW              { M_pow }
	| LSTCONS            { LstCons }
	| LSTCAT             { LstCat }
	| STRCAT             { StrCat }
	| SETDIFF            { SetDiff }
	| SETMEM             { SetMem }
	| SETSUB             { SetSub }
;

%inline unop_target:
	(* Unary minus defined in (l)expr_target *)
	| NOT         { Not }
	| BITWISENOT  { BitwiseNot }
	| M_ABS       { M_abs }
	| M_ACOS      { M_acos }
	| M_ASIN      { M_asin }
	| M_ATAN      { M_atan }
	| M_CEIL      { M_ceil }
	| M_COS       { M_cos }
	| M_EXP       { M_exp }
	| M_FLOOR     { M_floor }
	| M_LOG       { M_log }
	| M_ROUND     { M_round }
	| M_SGN       { M_sgn }
	| M_SIN       { M_sin }
	| M_SQRT      { M_sqrt }
	| M_TAN       { M_tan }
	| ISPRIMITIVE { IsPrimitive }
	| TOSTRING    { ToStringOp }
	| TOINT       { ToIntOp }
	| TOUINT16    { ToUint16Op }
	| TOINT32     { ToInt32Op }
	| TOUINT32    { ToUint32Op }
	| TONUMBER    { ToNumberOp }
	| CAR         { Car }
	| CDR         { Cdr }
	| LSTLEN      { LstLen }
	| STRLEN      { StrLen }
;

%inline constant_target:
	| MIN_FLOAT { Min_float }
	| MAX_FLOAT { Max_float }
	| RANDOM    { Random }
	| E         { E }
	| LN10      { Ln10 }
	| LN2       { Ln2 }
	| LOG2E     { Log2e }
	| LOG10E    { Log10e }
	| PI        { Pi }
	| SQRT1_2   { Sqrt1_2 }
	| SQRT2     { Sqrt2 }
	| UTCTIME   { UTCTime }
	| LOCALTIME { LocalTime }
;

%inline type_target:
	| UNDEFTYPELIT { UndefinedType }
	| NULLTYPELIT  { NullType }
	| EMPTYTYPELIT { EmptyType }
	| NONETYPELIT  { NoneType }
	| BOOLTYPELIT  { BooleanType }
	| NUMTYPELIT   { NumberType }
	| STRTYPELIT   { StringType }
	| OBJTYPELIT   { ObjectType }
	| LISTTYPELIT  { ListType }
	| TYPETYPELIT  { TypeType }
	| SETTYPELIT   { SetType }
;



(** JS Assertions - Copy Paste for YOUR LIFE **)
top_level_js_assertion_target:
	a = js_assertion_target; EOF { a }

js_assertion_target:
(* P /\ Q *)
	| left_ass=js_assertion_target; LAND; right_ass=js_assertion_target
		{ JSLAnd (left_ass, right_ass) }
(* P \/ Q *)
	| left_ass=js_assertion_target; LOR; right_ass=js_assertion_target
		{ JSLOr (left_ass, right_ass) }
(* ! Q *)
	| LNOT; ass=js_assertion_target
		{ JSLNot (ass) }
(* true *)
  | LTRUE
		{ JSLTrue }
(* false *)
  | LFALSE
		{ JSLFalse }
(* E == E *)
	| left_expr=js_lexpr_target; LEQUAL; right_expr=js_lexpr_target
		{ JSLEq (left_expr, right_expr) }
(* E <# E *)
	| left_expr=js_lexpr_target; LLESSTHAN; right_expr=js_lexpr_target
		{ JSLLess (left_expr, right_expr) }
(* E <=# E *)
	| left_expr=js_lexpr_target; LLESSTHANEQUAL; right_expr=js_lexpr_target
		{ JSLLessEq (left_expr, right_expr) }
(* E <s# E *)
	| left_expr=js_lexpr_target; LLESSTHANSTRING; right_expr=js_lexpr_target
		{ JSLStrLess (left_expr, right_expr) }
(* P * Q *)
(* The precedence of the separating conjunction is not the same as the arithmetic product *)
	| left_ass=js_assertion_target; TIMES; right_ass=js_assertion_target
		{ JSLStar (left_ass, right_ass) } %prec separating_conjunction
(* (E, E) -> E *)
	| LBRACE; obj_expr=js_lexpr_target; COMMA; prop_expr=js_lexpr_target; RBRACE; LARROW; val_expr=js_lexpr_target
		{ JSLPointsTo (obj_expr, prop_expr, val_expr) }
(* emp *)
	| LEMP;
		{ JSLEmp }
(* x(e1, ..., en) *)
	| name = VAR; LBRACE; params = separated_list(COMMA, js_lexpr_target); RBRACE
	  {
			(* validate_pred_assertion (name, params); *)
			JSLPred (name, params)
		}
(* forall X, Y, Z . P *)
	| LFORALL; vars = separated_nonempty_list(COMMA, lvar_type_target); DOT; ass = js_assertion_target
		{ JSLForAll (vars, ass) }
(* types (type_pairs) *)
  | LTYPES; LBRACE; type_pairs = separated_list(COMMA, js_type_env_pair_target); RBRACE
    { JSLTypes type_pairs }
(* scope(x: le) *)
	| SCOPE; LBRACE; v=VAR; COLON; le=js_lexpr_target; RBRACE
		{ JSLScope (v, le) }
(* E --e-- E *)
	| left_expr=js_lexpr_target; LSETMEM; right_expr=js_lexpr_target
		{ JSLSetMem (left_expr, right_expr) }
(* E --s-- E *)
	| left_expr=js_lexpr_target; LSETSUB; right_expr=js_lexpr_target
		{ JSLSetSub (left_expr, right_expr) }
(* fun_obj (x, le, le) *)
	| FUNOBJ; LBRACE; f_id=VAR; COMMA; f_loc=js_lexpr_target; COMMA; f_prototype=js_lexpr_target; f_scope_chain=option(js_lexpr_preceded_by_comma_target); RBRACE
		{ JSFunObj(f_id, f_loc, f_prototype, f_scope_chain) }
(* closure(x_0: le_0, ..., x_n: le_n; fid_0: le_0', ..., fid_n: le_n') *)
	| CLOSURE; LBRACE; var_les=separated_list(COMMA, var_js_le_pair_target); SCOLON; fid_scs=separated_list(COMMA, var_js_le_pair_target); RBRACE
		{	JSClosure (var_les, fid_scs)	}
(* sc_scope(pid, x: le1, le2) *)
	| SCSCOPE; LBRACE; pid=VAR; COMMA; x=VAR; COLON; le1=js_lexpr_target; COMMA; le2=js_lexpr_target; RBRACE
		{ JSLVarSChain (pid, x, le1, le2) }
(* o_chains(pid1: le1, pid2: le2) *)
	| OCHAINS; LBRACE; pid1=VAR; COLON; le1=js_lexpr_target; COMMA; pid2=VAR; COLON; le2=js_lexpr_target; RBRACE
		{ JSOSChains (pid1, le1, pid2, le2) }
(* empty_fields (le : lit1, lit2, lit3, ...) *)
	| EMPTYFIELDS; LBRACE; le=js_lexpr_target; COLON; fields=separated_list(COMMA, js_lexpr_target); RBRACE
		{ JSEmptyFields (le, fields) }
(* (P) *)
  | LBRACE; ass=js_assertion_target; RBRACE
	  { ass }
;

var_js_le_pair_target: 
	v=VAR; COLON; le=js_lexpr_target { (v, le) }
	

js_lexpr_preceded_by_comma_target: 
	COMMA; le=js_lexpr_target	{ le }
; 

js_program_variable_target:
  | v = VAR
	  { let _ = validate_pvar v in v }
	| RET
	  { let _ = validate_pvar "ret" in "ret" }
	| ERR
	  { let _ = validate_pvar "err" in "err" }
;

js_lexpr_target:
(* Logic literal *)
	| lit = lit_target
	  { (* Printf.printf "JS literal: %s" (JSIL_Print.string_of_literal lit false); *) JSLLit lit }
(* None *)
	| LNONE
	  { JSLNone }
(* program variable *)
	| pvar = js_program_variable_target
	  { JSPVar pvar }
(* Logic variable *)
	| lvar = LVAR
	  { JSLVar lvar }
(* e binop e *)
	| e1=js_lexpr_target; bop=binop_target; e2=js_lexpr_target
		{ JSLBinOp (e1, bop, e2) }
(* unop e *)
  | uop=unop_target; e=js_lexpr_target
		{ JSLUnOp (uop, e) }
(* - e *)
(* Unary negation has the same precedence as logical not, not as binary negation. *)
	| MINUS; e=js_lexpr_target
		{ JSLUnOp (UnaryMinus, e) } %prec unary_minus
(* typeOf *)
	| TYPEOF; LBRACE; e=js_lexpr_target; RBRACE
		{ JSLTypeOf (e) }
(* {{ e, ..., e }} *)
	| LSTOPEN; exprlist = separated_nonempty_list(COMMA, js_lexpr_target); LSTCLOSE
		{ JSLEList exprlist }
(* -{- e, ..., e -}- *)
	| SETOPEN; exprlist = separated_list(COMMA, js_lexpr_target); SETCLOSE
		{ JSLESet (JSSExpr.elements (JSSExpr.of_list exprlist)) }
(* l-nth(e1, e2) *)
	| LSTNTH; LBRACE; e1=js_lexpr_target; COMMA; e2=js_lexpr_target; RBRACE
		{ JSLLstNth (e1, e2) }
(* s-nth(e1, e2) *)
	| STRNTH; LBRACE; e1=js_lexpr_target; COMMA; e2=js_lexpr_target; RBRACE
		{ JSLStrNth (e1, e2) }
(* this *)
	| THIS { JSLThis }
(* Set union and intersection *)
	| SETUNION LBRACE; le = separated_list(COMMA, js_lexpr_target); RBRACE
	  { JSLSetUnion (JSSExpr.elements (JSSExpr.of_list le)) }
	| SETINTER LBRACE; le = separated_list(COMMA, js_lexpr_target); RBRACE
	  { JSLSetInter (JSSExpr.elements (JSSExpr.of_list le)) }
(* (e) *)
  | LBRACE; e=js_lexpr_target; RBRACE
	  { e }
;

js_type_env_pair_target:
  | v = VAR; COLON; the_type=type_target
    { (v, the_type) }
  | v = LVAR; COLON; the_type=type_target
    { (v, the_type) }
;



