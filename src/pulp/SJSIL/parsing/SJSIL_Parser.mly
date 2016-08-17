%{
open SJSIL_Syntax
%}

(* procedures *) 
%token IMPORT
%token PROC
%token RET
%token ERR
%token SPEC
%token NORMAL
(*literals*)
%token <string> LVAR
%token <string> VAR
(* %token <int> INT *)
%token <float> FLOAT
%token <string> STRING
%token <string> LOC
%token TRUE
%token FALSE
%token NULL 
%token UNDEFINED
%token EMPTY
%token LNONE
%token LNIL
%token NAN
%token INFINITY
(* Type literals *)
%token UNDEFTYPELIT
%token NULLTYPELIT
%token EMPTYTYPELIT
%token BOOLTYPELIT
%token NUMTYPELIT
%token STRTYPELIT
%token OBJTYPELIT
%token REFTYPELIT
%token VREFTYPELIT
%token OREFTYPELIT
%token LISTTYPELIT
%token TYPETYPELIT
(* command keywords  *)
%token PHI
%token PSI
%token GOTO
%token SKIP
%token DEFEQ
%token NEW
%token DELETE
%token HASFIELD
%token WITH
(* assertion keywords *)
%token LAND
%token LOR
%token LNOT
%token LTRUE
%token LFALSE
%token LEQUAL
%token LLESSTHANEQUAL
%token LARROW
%token LEMP 
%token LEXISTS 
%token LFORALL
(* expression keywords *)
%token VREF
%token OREF
%token BASE
%token FIELD
%token TYPEOF
%token CONS
%token ASSUME
%token ASSERT
%token RNUMSYM
%token RSTRSYM
(* binary operators *)
%token EQUAL
%token LESSTHAN
%token LESSTHANSTRING
%token LESSTHANEQUAL
%token PLUS
%token MINUS
%token TIMES
%token DIV
%token MOD
%token SUBTYPE
%token CONCAT
%token APPEND
%token AND
%token OR
%token BITWISEAND
%token BITWISEOR
%token BITWISEXOR
%token LEFTSHIFT
%token SIGNEDRIGHTSHIFT
%token UNSIGNEDRIGHTSHIFT
%token LCONS
%token SNTH
%token LNTH
%token M_ATAN2
%token M_POW
(* unary operators *)
%token NOT
%token TOSTRING
%token TONUMBER
%token TOINT
%token TOUINT16
%token TOINT32
%token TOUINT32
%token BITWISENOT
%token CAR
%token CDR
%token ISPRIMITIVE
%token LENGTH
%token GETFIELDS
%token ARGUMENTS
%token APPLY
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
%token M_SIN 
%token M_SGN
%token M_SQRT 
%token M_TAN 
%token M_RANDOM
(* constants *)
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
(* separators *)
%token EOF
%token COMMA
%token COLON
%token SCOLON
%token DOT
%token LBRACE
%token RBRACE
%token VREFLIT
%token OREFLIT
%token LBRACKET
%token RBRACKET
%token CLBRACKET
%token CRBRACKET
%token OSPEC
%token CSPEC
%token LISTOPEN
%token LISTCLOSE
(* symbolics *)
%token PRED
%token LTYPEENV

%type <((SJSIL_Syntax.jsil_metadata * string option * SJSIL_Syntax.jsil_lab_cmd) list)> cmd_list_top_target
%type <SJSIL_Syntax.jsil_ext_procedure> proc_target
%type <SJSIL_Syntax.jsil_ext_program> main_target

%start main_target proc_target cmd_list_top_target
%%

(********* JSIL *********)

main_target:
    import_target declaration_target
		{ (* Add the imports to the program *)
	  	{$2 with imports = $1}
		}
	| declaration_target { $1 }
	;

declaration_target:
	  pred_target declaration_target
		{ (* Add the predicate to the hash table of predicates *)
			Hashtbl.add $2.predicates $1.name $1;
			$2
		}
	| proc_target declaration_target
		{ (* Add the procedure to the hash table of procedures *)
			Hashtbl.replace $2.procedures $1.lproc_name $1; (* Warn if conflicting names? *)
			$2
		}
	| EOF
		{ (* Return an empty program *)
			{ imports = []; predicates = Hashtbl.create 64; procedures = Hashtbl.create 64; }
		}
	;

import_target: 
  IMPORT; imports=separated_list(COMMA, VAR); SCOLON { imports } 

proc_target: 
(* [spec;] proc xpto (x, y) { cmd_list[;] } with { ret: x, i; [err: x, j] }; *) 
  spec = option(spec_target);
	PROC; proc_name=VAR; LBRACE; param_list=param_list_target; RBRACE; 
		CLBRACKET; cmd_list=cmd_list_target; option(SCOLON); CRBRACKET; 
	WITH; 
		CLBRACKET; ctx_ret=option(ctx_target_ret); ctx_err=option(ctx_target_err); CRBRACKET; option(SCOLON)
	{
		(* Printf.printf "Parsing Procedure.\n"; *)
		(match (spec : SJSIL_Syntax.jsil_spec option) with
		| None -> ()
		| Some specif ->  if (not (specif.spec_name = proc_name))    then (raise (Failure "Specification name does not match procedure name."))           else 
			               (if (not (specif.spec_params = param_list)) then (raise (Failure "Specification parameters do not match procedure parameters.")) else ())
		);
		let ret_var, ret_index = 
		(match ctx_ret with 
			| None -> None, None
			| Some (rv, ri) -> Some rv, Some ri) in 
		let err_var, err_index = 
			(match ctx_err with 
			| None -> None, None
			| Some (ev, ei) -> Some ev, Some ei) in
		let cmd_arr = Array.of_list cmd_list in 
		{
    	SJSIL_Syntax.lproc_name = proc_name;
    	SJSIL_Syntax.lproc_body = cmd_arr;
    	SJSIL_Syntax.lproc_params = param_list; 
			SJSIL_Syntax.lret_label = ret_index;
			SJSIL_Syntax.lret_var = ret_var;
			SJSIL_Syntax.lerror_label = err_index;
			SJSIL_Syntax.lerror_var = err_var;
			SJSIL_Syntax.lspec = spec;
		}
	};

ctx_target_ret: 
(* ret: x, i; *)
	RET; COLON; ret_v=VAR; COMMA; i=VAR; SCOLON;
	{ 
		(* Printf.printf "Parsing return context.\n"; *)
		ret_v, i
	}
	
ctx_target_err: 
(* err: x, j *)
	ERR; COLON; err_v=VAR; COMMA; j=VAR; SCOLON;
	{ 
		(* Printf.printf "Parsing error context.\n"; *)	
		err_v, j
	}

param_list_target: 
	param_list = separated_list(COMMA, VAR) { param_list };

cmd_list_target: 
	cmd_list = separated_list(SCOLON, cmd_with_label_and_specs) {
		List.rev 
			(List.fold_left
				(fun ac c ->
					match c with
			 		| (None, None, None) -> ac
					| (pre, lab, Some v) -> 
						let metadata = make_jsil_metadata None pre in 
						(metadata, lab, v) :: ac
          | _, _, _ -> raise (Failure "Yeah, that's not really going to work without a command.")
				)
				[] 
				cmd_list)
	};

cmd_list_top_target: 
	cmd_list = separated_list(SCOLON, cmd_with_label_and_specs); EOF {
		List.rev 
			(List.fold_left
				(fun ac c ->
					match c with
			 		| (None, None, None) -> ac
					| (pre, lab, Some v) -> 
						let metadata = make_jsil_metadata None pre in 
						(metadata, lab, v) :: ac
          | _, _, _ -> raise (Failure "Yeah, that's not really going to work without a command.")
				)
				[] 
				cmd_list)
	};

cmd_with_label_and_specs:
  | pre = option(spec_line); cmd = cmd_target
		{ (pre, None, cmd) }
		
	| pre = option(spec_line); lab = label; cmd = cmd_target; 
		{ (pre, Some lab, cmd) }

cmd_target: 
(* skip *)
	| SKIP 
		{ 
			(* Printf.printf "Parsing Skip.\n"; *)
			Some (SJSIL_Syntax.SLBasic(SJSIL_Syntax.SSkip))
		} 
(* x := new() *) 
	| v=VAR; DEFEQ; NEW; LBRACE; RBRACE
		{ 
			(* Printf.printf "Parsing New.\n"; *)
			Some (SJSIL_Syntax.SLBasic (SJSIL_Syntax.SNew v))
		}
(* x := e *)
	| v=VAR; DEFEQ; e=expr_target 
	{ 
		(* Printf.printf "Parsing Assignment.\n"; *)
		Some (SJSIL_Syntax.SLBasic (SJSIL_Syntax.SAssignment (v, e)))
	}

(* x := PHI(e1, e2, ... en); *)
  | v=VAR; DEFEQ; PHI; LBRACE; es = param_list_target; RBRACE
	  {
			(* Printf.printf "Parsing PHI-node.\n"; *)
			let rec oes l =
				(match l with
				| [] -> []
				| x :: l -> Some x :: oes l) in
			Some (SLPhiAssignment (v, Array.of_list (oes es)))
		}

(* x := PSI(e1, e2, ... en); *)
  | v=VAR; DEFEQ; PSI; LBRACE; es = param_list_target; RBRACE
	  {
			(* Printf.printf "Parsing PSI-node.\n"; *)
			let rec oes l =
				(match l with
				| [] -> []
				| x :: l -> Some x :: oes l) in
			Some (SLPsiAssignment (v, Array.of_list (oes es)))
		}	
			
(* x := [e1, e2] *)
	| v=VAR; DEFEQ; LBRACKET; e1=expr_target; COMMA; e2=expr_target; RBRACKET 
		{ 
			(* Printf.printf "Parsing Field Look-up.\n"; *)
			Some (SJSIL_Syntax.SLBasic (SJSIL_Syntax.SLookup (v, e1, e2)))
		}
(* [e1, e2] := e3 *)
	| LBRACKET; e1=expr_target; COMMA; e2=expr_target; RBRACKET; DEFEQ; e3=expr_target    
		{ 
			(* Printf.printf "Parsing Field Assignment.\n"; *)
			Some (SJSIL_Syntax.SLBasic (SJSIL_Syntax.SMutation (e1, e2, e3))) 
		}
(* delete(e1, e2) *)
	| DELETE; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
		{ 
			(* Printf.printf "Parsing Deletion.\n"; *)
			Some (SJSIL_Syntax.SLBasic (SJSIL_Syntax.SDelete (e1, e2)))
		}
(* x := hasField(e1, e2) *)
	| v=VAR; DEFEQ; HASFIELD; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
		{ 
			(* Printf.printf "Parsing HasField.\n"; *)
			Some (SJSIL_Syntax.SLBasic (SJSIL_Syntax.SHasField (v, e1, e2)))
		}
(* x := getFields (e1) *)
	| v = VAR; DEFEQ; GETFIELDS; LBRACE; e=expr_target; RBRACE
		{ Some (SJSIL_Syntax.SLBasic (SGetFields (v, e))) }
(* x := args *)
	| v = VAR; DEFEQ; ARGUMENTS
	  {
			Some (SJSIL_Syntax.SLBasic (SArguments v))
		}
(* goto i *)
	| GOTO; i=VAR 
		{
			(* Printf.printf "Parsing Goto.\n"; *)
			Some (SJSIL_Syntax.SLGoto i)
		}
(* goto [e] i j *)
	| GOTO LBRACKET; e=expr_target; RBRACKET; i=VAR; j=VAR 
		{
			(* Printf.printf "Parsing Conditional Goto.\n"; *)
			Some (SJSIL_Syntax.SLGuardedGoto (e, i, j))
		}
(* x := e(e1, ..., en) with j *)
	| v=VAR; DEFEQ; e=expr_target; LBRACE; es=expr_list_target; RBRACE; oi = option(call_with_target)
		{
			(* Printf.printf "Parsing Procedure Call.\n"; *)
			Some (SJSIL_Syntax.SLCall (v, e, es, oi))
		};
(* x := apply (e1, ..., en) with j *)
	| v=VAR; DEFEQ; APPLY; LBRACE; es=expr_list_target; RBRACE; oi = option(call_with_target)
		{
			(* Printf.printf "Parsing Procedure Call.\n"; *)
			Some (SJSIL_Syntax.SLApply (v, es, oi))
		}
;

label: 
	lab=VAR; COLON; 
		{ lab }

expr_list_target: 
	expr_list=separated_list(COMMA, expr_target) { expr_list }
;

expr_target: 
(* literal *)
	| lit=lit_target { SJSIL_Syntax.Literal lit }
(* var *)
	| v=VAR { SJSIL_Syntax.Var v }
(* binop *)	
	| e1=expr_target; bop=binop_target; e2=expr_target { SJSIL_Syntax.BinOp (e1, bop, e2) }
(* unop *)
  | uop=unop_target; e=expr_target { SJSIL_Syntax.UnaryOp (uop, e) }
(* vref *)
	| VREF; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
		{ SJSIL_Syntax.VRef (e1, e2) }
(* oref *)
	| OREF; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
		{ SJSIL_Syntax.ORef (e1, e2) }
(* base *)
	| BASE; LBRACE; e=expr_target; RBRACE
		{ SJSIL_Syntax.Base (e) }
(* field *)
	| FIELD; LBRACE; e=expr_target; RBRACE
		{ SJSIL_Syntax.Field (e) }		
(* typeof *)
	| TYPEOF; LBRACE; e=expr_target; RBRACE
		{ SJSIL_Syntax.TypeOf (e) }
(* s-nth (string, n) *)
	| SNTH; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE 
		{ SJSIL_Syntax.SNth (e1, e2) }
(* l-nth (list, n) *)
	| LNTH; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE 
		{ SJSIL_Syntax.LNth (e1, e2) }
(* {{ }}	| LISTOPEN; LISTCLOSE { SJSIL_Syntax.LEList [] } *)
(* {{ e, ..., e }} *)
	| LISTOPEN; exprlist = separated_list(COMMA, expr_target); LISTCLOSE 
		{ SJSIL_Syntax.EList exprlist }
(* cons(e, e) *)
	| LISTOPEN; CONS; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE 
		{ SJSIL_Syntax.Cons (e1, e2) }
(* (e) *)
  | LBRACE; e=expr_target; RBRACE
		{ e }
(* asssume (e) *)
  | ASSUME; LBRACE; e=expr_target; RBRACE
	  { SJSIL_Syntax.RAssume (e) }	
(* assert (e) *)
  | ASSERT; LBRACE;  e=expr_target; RBRACE
	  { SJSIL_Syntax.RAssert (e) }
(* make_symbol_number() *)
  | RNUMSYM; LBRACE;  RBRACE
	  { SJSIL_Syntax.RNumSymb }		
(* make_symbol_string() *)
  | RSTRSYM; LBRACE; RBRACE
	  { SJSIL_Syntax.RStrSymb }		
;

(********* LOGIC *********)

pred_target:
	PRED name=VAR LBRACE params=param_list_target RBRACE COLON
		definitions=separated_list(COMMA, assertion_target) SCOLON
  {
		{
			name        = name;
			num_params  = List.length params;
			params      = params;
			definitions = definitions;
		}
	};

spec_target: 
(* spec xpto (x, y) pre: assertion, post: assertion, flag: NORMAL|ERROR *) 
	SPEC; proc_name=VAR; LBRACE; param_list=param_list_target; RBRACE; pre_post_list=pre_post_list_target;
	{ 
		{ 
      spec_name = proc_name;
    	spec_params = param_list;
			proc_specs = pre_post_list 
		}
	};
	
pre_post_list_target:
	pre_post_list = separated_list(SCOLON, pre_post_target) { pre_post_list };

(* [[ .... ]] [[ .... ]] flag *)
pre_post_target:
	pre_assertion = spec_line; post_assertion = spec_line; ret_flag=ret_flag_target
	{
		{
			pre = pre_assertion;
			post = post_assertion;
			ret_flag = ret_flag
		}
	};

spec_line:
  OSPEC; assertion=assertion_target; CSPEC
	{ assertion }

ret_flag_target: 
	| NORMAL { Normal }
	| ERR { Error }
; 

assertion_target:
(* P /\ Q *)
	| left_ass=assertion_target; LAND; right_ass=assertion_target 
		{ LAnd (left_ass, right_ass) }
(* P \/ Q *)
	| left_ass=assertion_target; LOR; right_ass=assertion_target 
		{ LOr (left_ass, right_ass) }
(* ~ Q *)
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
(* E <== E *)
	| left_expr=lexpr_target; LLESSTHANEQUAL; right_expr=lexpr_target
		{ LLessEq (left_expr, right_expr) }
(* P * Q *)
	| left_ass=assertion_target; TIMES; right_ass=assertion_target 
		{ 
			LStar (left_ass, right_ass) 
		}
(* (E, E) -> E *)
	| LBRACE; obj_expr=lexpr_target; COMMA; prop_expr=lexpr_target; RBRACE; LARROW; val_expr=lexpr_target
		{ 
			LPointsTo (obj_expr, prop_expr, val_expr) 
		}
(* emp *)
	| LEMP;
		{ 
			LEmp 
		}
(* exists X, Y, Z . P *)
	| LEXISTS; vars=var_list_target; DOT; ass=assertion_target
		{ LExists (vars, ass) }
(* forall X, Y, Z . P *)
	| LFORALL; vars=var_list_target; DOT; ass=assertion_target
		{ LForAll (vars, ass) }
		
(* type_env (type_pairs) *)
  | LTYPEENV; LBRACE; type_pairs = type_env_pair_list_target; RBRACE
    { LTypeEnv type_pairs }

(* (P) *)
  | LBRACE; ass=assertion_target; RBRACE
	  { ass }
;

var_target:
  | pv = VAR  { PVar pv }
	| lv = LVAR { LVar lv }
;

type_env_pair_list_target:
  type_env_pair_list = separated_list(COMMA, type_env_pair_target) { type_env_pair_list; }
;

type_env_pair_target:
  | v = var_target; COLON; the_type=jsil_type_target
	  { (v, the_type) }
;

jsil_type_target:
	| UNDEFTYPELIT { SJSIL_Syntax.UndefinedType }
	| NULLTYPELIT { SJSIL_Syntax.NullType }
  | EMPTYTYPELIT { SJSIL_Syntax.EmptyType }
	| BOOLTYPELIT { SJSIL_Syntax.BooleanType }
	| NUMTYPELIT { SJSIL_Syntax.NumberType }
	| STRTYPELIT { SJSIL_Syntax.StringType }
	| OBJTYPELIT { SJSIL_Syntax.ObjectType }
	| REFTYPELIT { SJSIL_Syntax.ReferenceType }
	| VREFTYPELIT { SJSIL_Syntax.VariableReferenceType }
	| OREFTYPELIT { SJSIL_Syntax.ObjectReferenceType }	
	| LISTTYPELIT { SJSIL_Syntax.ListType }
  | TYPETYPELIT { SJSIL_Syntax.TypeType }
;

var_list_target:
	var_list = separated_list(COMMA, LVAR) { var_list }
;

lexpr_target:
(* literal *)
	| lit=lit_target { LLit lit }
(* none *)
	| LNONE
		{ LNone }
(* lvar *)
	| v=LVAR { LVar v }
(* pvar *)
	| v=VAR { PVar v }
(* binop *)	
	| e1=lexpr_target; bop=binop_target; e2=lexpr_target { LBinOp (e1, bop, e2) }
(* unop *)
  | uop=unop_target; e=lexpr_target { LUnOp (uop, e) }
(* vref *)
	| VREF; LBRACE; e1=lexpr_target; COMMA; e2=lexpr_target; RBRACE
		{ LEVRef (e1, e2) }
(* oref *)
	| OREF; LBRACE; e1=lexpr_target; COMMA; e2=lexpr_target; RBRACE
		{ LEORef (e1, e2) }
(* base *)
	| BASE; LBRACE; e=lexpr_target; RBRACE
		{ LBase (e) }
(* field *)
	| FIELD; LBRACE; e=lexpr_target; RBRACE
		{ LBase (e) }		
(* typeof *)
	| TYPEOF; LBRACE; e=lexpr_target; RBRACE
		{ LTypeOf (e) }
(* l-nth(e1, e2) *)
	| LNTH; LBRACE; e1=lexpr_target; COMMA; e2=lexpr_target; RBRACE { SJSIL_Syntax.LLNth (e1, e2) }
(* s-nth(e1, e2) *)
	| SNTH; LBRACE; e1=lexpr_target; COMMA; e2=lexpr_target; RBRACE { SJSIL_Syntax.LSNth (e1, e2) }
(* {{ e, ..., e }} *)
	| LISTOPEN; exprlist = separated_list(COMMA, lexpr_target); LISTCLOSE 
		{ SJSIL_Syntax.LEList exprlist }
(* cons(e, e) *)
	| LISTOPEN; CONS; LBRACE; e1=lexpr_target; COMMA; e2=lexpr_target; RBRACE 
		{ SJSIL_Syntax.LCons (e1, e2) }
(* (e) *)
  | LBRACE; e=lexpr_target; RBRACE
	  { e }	
;		

(********* COMMON *********)

lit_target: 
	| UNDEFINED { SJSIL_Syntax.Undefined }
	| NULL { SJSIL_Syntax.Null }
	| EMPTY { SJSIL_Syntax.Empty }
	| UNDEFTYPELIT { SJSIL_Syntax.Type SJSIL_Syntax.UndefinedType }
	| NULLTYPELIT { SJSIL_Syntax.Type SJSIL_Syntax.NullType }
  | EMPTYTYPELIT { SJSIL_Syntax.Type SJSIL_Syntax.EmptyType }
	| BOOLTYPELIT { SJSIL_Syntax.Type SJSIL_Syntax.BooleanType }
	| NUMTYPELIT { SJSIL_Syntax.Type SJSIL_Syntax.NumberType }
	| STRTYPELIT { SJSIL_Syntax.Type SJSIL_Syntax.StringType }
	| OBJTYPELIT { SJSIL_Syntax.Type SJSIL_Syntax.ObjectType }
	| REFTYPELIT { SJSIL_Syntax.Type SJSIL_Syntax.ReferenceType }
	| VREFTYPELIT { SJSIL_Syntax.Type SJSIL_Syntax.VariableReferenceType }
	| OREFTYPELIT { SJSIL_Syntax.Type SJSIL_Syntax.ObjectReferenceType }	
	| LISTTYPELIT { SJSIL_Syntax.Type SJSIL_Syntax.ListType }
	| TYPETYPELIT { SJSIL_Syntax.Type SJSIL_Syntax.TypeType }
	| TRUE { SJSIL_Syntax.Bool true }
	| FALSE { SJSIL_Syntax.Bool false }
(*	| i=INT { SJSIL_Syntax.Num (float_of_int i) } *)
	| NAN { SJSIL_Syntax.Num nan }
	| INFINITY { SJSIL_Syntax.Num infinity }
	| x=FLOAT { SJSIL_Syntax.Num x }
	| s=STRING { SJSIL_Syntax.String s }
	| loc=LOC { SJSIL_Syntax.Loc loc }
	| loc=lit_target; VREFLIT; s=STRING { SJSIL_Syntax.LVRef (loc, s) }
	| loc=lit_target; OREFLIT; s=STRING { SJSIL_Syntax.LORef (loc, s) }
	(* EMPTY AND NON-EMPTY LISTS *)
	| LNIL { SJSIL_Syntax.LList [] }
	| LISTOPEN; LISTCLOSE { SJSIL_Syntax.LList [] }
	| MIN_FLOAT { SJSIL_Syntax.Constant Min_float }
	| MAX_FLOAT { SJSIL_Syntax.Constant Max_float }
	| RANDOM { SJSIL_Syntax.Constant Random }
	| E { SJSIL_Syntax.Constant E }
	| LN10 { SJSIL_Syntax.Constant Ln10 }
	| LN2 { SJSIL_Syntax.Constant Ln2 }
	| LOG2E { SJSIL_Syntax.Constant Log2e }
	| LOG10E { SJSIL_Syntax.Constant Log10e }
	| PI { SJSIL_Syntax.Constant Pi }
	| SQRT1_2 { SJSIL_Syntax.Constant Sqrt1_2 }
	| SQRT2 { SJSIL_Syntax.Constant Sqrt2 }
	| M_RANDOM { SJSIL_Syntax.Constant Random }
;

binop_target: 
	| EQUAL { SJSIL_Syntax.Equal }
	| LESSTHAN { SJSIL_Syntax.LessThan }
	| LESSTHANSTRING { SJSIL_Syntax.LessThanString }
	| LESSTHANEQUAL { SJSIL_Syntax.LessThanEqual }
	| PLUS { SJSIL_Syntax.Plus }
	| MINUS { SJSIL_Syntax.Minus }
	| TIMES { SJSIL_Syntax.Times }
	| DIV { SJSIL_Syntax.Div }
	| MOD { SJSIL_Syntax.Mod }
	| SUBTYPE { SJSIL_Syntax.Subtype }
	| CONCAT { SJSIL_Syntax.Concat }
	| APPEND { SJSIL_Syntax.Append }
	| AND { SJSIL_Syntax.And }
	| OR { SJSIL_Syntax.Or }
	| BITWISEAND { SJSIL_Syntax.BitwiseAnd }
	| BITWISEOR { SJSIL_Syntax.BitwiseOr}
	| BITWISEXOR { SJSIL_Syntax.BitwiseXor }
	| LEFTSHIFT { SJSIL_Syntax.LeftShift }
	| SIGNEDRIGHTSHIFT { SJSIL_Syntax.SignedRightShift }
	| UNSIGNEDRIGHTSHIFT { SJSIL_Syntax.UnsignedRightShift }
	| LCONS { SJSIL_Syntax.LCons }
	| M_ATAN2 { SJSIL_Syntax.M_atan2 }
	| M_POW {SJSIL_Syntax.M_pow }
;

unop_target: 
	| NOT { SJSIL_Syntax.Not }
	| MINUS { SJSIL_Syntax.Negative }
	| TOSTRING { SJSIL_Syntax.ToStringOp }
	| TONUMBER { SJSIL_Syntax.ToNumberOp }
	| TOINT { SJSIL_Syntax.ToIntOp }
	| TOUINT16 { SJSIL_Syntax.ToUint16Op }
	| TOINT32 { SJSIL_Syntax.ToInt32Op }
	| TOUINT32 { SJSIL_Syntax.ToUint32Op }
	| BITWISENOT { SJSIL_Syntax.BitwiseNot }
	| CAR { SJSIL_Syntax.Car }
	| CDR { SJSIL_Syntax.Cdr }
	| ISPRIMITIVE { SJSIL_Syntax.IsPrimitive }
	| LENGTH { SJSIL_Syntax.Length }
	| M_ABS   { SJSIL_Syntax.M_abs }
	| M_ACOS  { SJSIL_Syntax.M_acos }
	| M_ASIN  { SJSIL_Syntax.M_asin }
	| M_ATAN  { SJSIL_Syntax.M_atan }
	| M_CEIL  { SJSIL_Syntax.M_ceil }
	| M_COS   { SJSIL_Syntax.M_cos }
	| M_EXP   { SJSIL_Syntax.M_exp }
	| M_FLOOR { SJSIL_Syntax.M_floor }
	| M_LOG   { SJSIL_Syntax.M_log }
	| M_ROUND { SJSIL_Syntax.M_round }
	| M_SGN   { SJSIL_Syntax.M_sgn }
	| M_SIN   { SJSIL_Syntax.M_sin }
	| M_SQRT  { SJSIL_Syntax.M_sqrt }
	| M_TAN   { SJSIL_Syntax.M_tan }
;

call_with_target: 
	WITH; i=VAR { i }