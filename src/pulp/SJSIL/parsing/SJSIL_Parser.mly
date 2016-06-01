%{
open SSyntax 
%}

(* procedures *) 
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
%token BOOLTYPELIT
%token NUMTYPELIT
%token STRTYPELIT
%token OBJTYPELIT
%token REFTYPELIT
%token VREFTYPELIT
%token OREFTYPELIT
%token LISTTYPELIT
(* command keywords  *)
%token GOTO
%token SKIP
%token DEFEQ
%token NEW
%token DELETE
%token HASFIELD
%token PROTOFIELD
%token PROTOOBJ
%token WITH
(* assertion keywords *)
%token LAND
%token LOR
%token LNOT
%token LTRUE
%token LFALSE
%token LEQUAL
%token LLESSTHANEQUAL	
(*%token LSTAR*)
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
(* binary operators *)
%token EQUAL
%token LESSTHAN
%token LESSTHANEQUAL
%token PLUS
%token MINUS
%token TIMES
%token DIV
%token MOD
%token SUBTYPE
%token CONCAT
%token AND
%token OR
%token BITWISEAND
%token BITWISEOR
%token BITWISEXOR
%token LEFTSHIFT
%token SIGNEDRIGHTSHIFT
%token UNSIGNEDRIGHTSHIFT
%token LCONS
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
%token M_SQRT 
%token M_TAN 
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

%type <(SSyntax.lprocedure list)> prog_target
%type <(SSyntax.jsil_spec list)>  specs_target
%type <((SSyntax.jsil_logic_assertion option * string option * SSyntax.jsil_lab_cmd) list)> cmd_list_top_target



(* main target <(SSyntax.lprocedure list)> *) 
%start prog_target specs_target cmd_list_top_target
%%

(********* JSIL *********)

prog_target: 
	proc_list_target EOF	{ $1 }
;

proc_list_target: 
	proc_list = separated_list(SCOLON, proc_target) { proc_list };

proc_target: 
(* [spec]; proc xpto (x, y) { cmd_list[;] } with { ret: x, i; [err: x, j] }; *) 
  spec = option(spec_target);
	PROC; proc_name=VAR; LBRACE; param_list=param_list_target; RBRACE; 
		CLBRACKET; cmd_list=cmd_list_target; option(SCOLON); CRBRACKET; 
	WITH; 
		CLBRACKET; ctx_ret=ctx_target_ret; ctx_err=option(ctx_target_err); CRBRACKET
	{
		Printf.printf "Parsing Procedure.\n";
		(match (spec : SSyntax.jsil_spec option) with
		| None -> ()
		| Some specif ->  if (not (specif.spec_name = proc_name))    then (raise (Failure "Specification name does not match procedure name."))           else 
			               (if (not (specif.spec_params = param_list)) then (raise (Failure "Specification parameters do not match procedure parameters.")) else ())
		);
		let ret_var, ret_index = ctx_ret in 
		let err_var, err_index = 
			(match ctx_err with 
			| None -> None, None
			| Some (ev, ei) -> Some ev, Some ei)						
			in
		let cmd_arr = Array.of_list cmd_list in 
		{
    	SSyntax.lproc_name = proc_name;
    	SSyntax.lproc_body = cmd_arr;
    	SSyntax.lproc_params = param_list; 
			SSyntax.lret_label = ret_index;
			SSyntax.lret_var = ret_var;
			SSyntax.lerror_label = err_index;
			SSyntax.lerror_var = err_var;
			SSyntax.lspec = spec;
		}
	};

ctx_target_ret: 
(* ret: x, i; *)
	RET; COLON; ret_v=VAR; COMMA; i=VAR; SCOLON;
	{ 
		Printf.printf "Parsing return context.\n";
		ret_v, i
	}
	
ctx_target_err: 
(* err: x, j *)
	ERR; COLON; err_v=VAR; COMMA; j=VAR; SCOLON;
	{ 
		Printf.printf "Parsing error context.\n";	
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
					| (pre, lab, Some v) -> (pre, lab, v) :: ac
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
					| (pre, lab, Some v) -> (pre, lab, v) :: ac
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
			Printf.printf "Parsing Skip.\n";
			Some (SSyntax.SLBasic(SSyntax.SSkip))
		} 
(* x := new() *) 
	| v=VAR; DEFEQ; NEW; LBRACE; RBRACE
		{ 
			Printf.printf "Parsing New.\n";
			Some (SSyntax.SLBasic (SSyntax.SNew v))
		}
(* x := e *)
	| v=VAR; DEFEQ; e=expr_target 
	{ 
		Printf.printf "Parsing Assignment.\n";
		Some (SSyntax.SLBasic (SSyntax.SAssignment (v, e)))
	}
(* x := [e1, e2] *)
	| v=VAR; DEFEQ; LBRACKET; e1=expr_target; COMMA; e2=expr_target; RBRACKET 
		{ 
			Printf.printf "Parsing Field Look-up.\n";
			Some (SSyntax.SLBasic (SSyntax.SLookup (v, e1, e2)))
		}
(* [e1, e2] := e3 *)
	| LBRACKET; e1=expr_target; COMMA; e2=expr_target; RBRACKET; DEFEQ; e3=expr_target    
		{ 
			Printf.printf "Parsing Field Assignemnt.\n";
			Some (SSyntax.SLBasic (SSyntax.SMutation (e1, e2, e3))) 
		}
(* delete(e1, e2) *)
	| DELETE; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
		{ 
			Printf.printf "Parsing Deletion.\n";
			Some (SSyntax.SLBasic (SSyntax.SDelete (e1, e2)))
		}
(* x := hasField(e1, e2) *)
	| v=VAR; DEFEQ; HASFIELD; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
		{ 
			Printf.printf "Parsing HasField.\n";
			Some (SSyntax.SLBasic (SSyntax.SHasField (v, e1, e2)))
		}
(* x := protoField(e1, e2) *)
	| v=VAR; DEFEQ; PROTOFIELD; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
		{ 
			Printf.printf "Parsing ProtoField.\n";
			Some (SSyntax.SLBasic (SSyntax.SProtoField (v, e1, e2)))
		}
(* x := protoObj(e1, e2) *)
	| v=VAR; DEFEQ; PROTOOBJ; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
		{ 
			Printf.printf "Parsing ProtoObj.\n";
			Some (SSyntax.SLBasic (SSyntax.SProtoObj (v, e1, e2)))
		}
	| v = VAR; DEFEQ; GETFIELDS; LBRACE; e=expr_target; RBRACE
		{ Some (SSyntax.SLBasic (SGetFields (v, e))) }
(* goto i *)
	| GOTO; i=VAR 
		{
			Printf.printf "Parsing Goto.\n";
			Some (SSyntax.SLGoto i)
		}
(* goto [e] i j *)
	| GOTO LBRACKET; e=expr_target; RBRACKET; i=VAR; j=VAR 
		{
			Printf.printf "Parsing Conditional Goto.\n";
			Some (SSyntax.SLGuardedGoto (e, i, j))
		}
(* x := e(e1, ..., en) with j *)
	| v=VAR; DEFEQ; e=expr_target; LBRACE; es=expr_list_target; RBRACE; oi = option(call_with_target)
		{
			Printf.printf "Parsing Procedure Call.\n";
			Some (SSyntax.SLCall (v, e, es, oi))
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
	| lit=lit_target { SSyntax.Literal lit }
(* var *)
	| v=VAR { SSyntax.Var v }
(* binop *)	
	| e1=expr_target; bop=binop_target; e2=expr_target { SSyntax.BinOp (e1, bop, e2) }
(* unop *)
  | uop=unop_target; e=expr_target { SSyntax.UnaryOp (uop, e) }
(* vref *)
	| VREF; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
		{ SSyntax.VRef (e1, e2) }
(* oref *)
	| OREF; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
		{ SSyntax.ORef (e1, e2) }
(* base *)
	| BASE; LBRACE; e=expr_target; RBRACE
		{ SSyntax.Base (e) }
(* field *)
	| FIELD; LBRACE; e=expr_target; RBRACE
		{ SSyntax.Field (e) }		
(* typeof *)
	| TYPEOF; LBRACE; e=expr_target; RBRACE
		{ SSyntax.TypeOf (e) }
(* nth *)
	| LNTH; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE { SSyntax.LLNth (e1, e2) }
(* {{ }} *)
 	| LISTOPEN; LISTCLOSE { SSyntax.LEList [] }
(* {{ e, ..., e }} *)
	| LISTOPEN; exprlist = separated_list(COMMA, expr_target); LISTCLOSE { SSyntax.LEList exprlist }
(* (e) *)
  | LBRACE; e=expr_target; RBRACE
		{ e }
;

(********* LOGIC *********)

specs_target:
	spec_list_target EOF	{ Printf.printf("Entering specs_target"); $1 }
;

spec_list_target: 
	spec_list = separated_list(SCOLON, spec_target) { spec_list };

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
(* (P) *)
  | LBRACE; ass=assertion_target; RBRACE
	  { ass }
;

var_list_target:
	var_list = separated_list(COMMA, LVAR) { var_list };

lexpr_target:
(* literal *)
	| lit=lit_target { LLit lit }
(* none *)
	| LNONE
		{ LNone }
(* [] *)
	| LBRACKET; RBRACKET
		{ LListEmpty }
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
(* cons *)
	| e1=lexpr_target; LCONS; e2=lexpr_target
		{ LLCons (e1, e2) }
(* (e) *)
  | LBRACE; e=lexpr_target; RBRACE
	  { e }
		
(********* COMMON *********)

lit_target: 
	| UNDEFINED { SSyntax.Undefined }
	| NULL { SSyntax.Null }
	| EMPTY { SSyntax.Empty }
	| BOOLTYPELIT { SSyntax.Type SSyntax.BooleanType }
	| NUMTYPELIT { SSyntax.Type SSyntax.NumberType }
	| STRTYPELIT { SSyntax.Type SSyntax.StringType }
	| OBJTYPELIT { SSyntax.Type SSyntax.ObjectType }
	| REFTYPELIT { SSyntax.Type SSyntax.ReferenceType }
	| VREFTYPELIT { SSyntax.Type SSyntax.VariableReferenceType }
	| OREFTYPELIT { SSyntax.Type SSyntax.ObjectReferenceType }	
	| LISTTYPELIT { SSyntax.Type SSyntax.ListType }
	| TRUE { SSyntax.Bool true }
	| FALSE { SSyntax.Bool false }
(*	| i=INT { SSyntax.Num (float_of_int i) } *)
	| NAN { SSyntax.Num nan }
	| INFINITY { SSyntax.Num infinity }
	| x=FLOAT { SSyntax.Num x }
	| s=STRING { SSyntax.String s }
	| loc=LOC { SSyntax.Loc loc }
	| loc=lit_target; VREFLIT; s=STRING { SSyntax.LVRef (loc, s) }
	| loc=lit_target; OREFLIT; s=STRING { SSyntax.LORef (loc, s) }
	(* EMPTY AND NON-EMPTY LISTS *)
	| LNIL { SSyntax.LList [] }
	| LISTOPEN; LISTCLOSE { SSyntax.LList [] }
	| MIN_FLOAT { SSyntax.Constant Min_float }
	| MAX_FLOAT { SSyntax.Constant Max_float }
	| RANDOM { SSyntax.Constant Random }
	| E { SSyntax.Constant E }
	| LN10 { SSyntax.Constant Ln10 }
	| LN2 { SSyntax.Constant Ln2 }
	| LOG2E { SSyntax.Constant Log2e }
	| LOG10E { SSyntax.Constant Log10e }
	| PI { SSyntax.Constant Pi }
	| SQRT1_2 { SSyntax.Constant Sqrt1_2 }
	| SQRT2 { SSyntax.Constant Sqrt2 }
;

binop_target: 
	| EQUAL { SSyntax.Equal }
	| LESSTHAN { SSyntax.LessThan }
	| LESSTHANEQUAL { SSyntax.LessThanEqual }
	| PLUS { SSyntax.Plus }
	| MINUS { SSyntax.Minus }
	| TIMES { SSyntax.Times }
	| DIV { SSyntax.Div }
	| MOD { SSyntax.Mod }
	| SUBTYPE { SSyntax.Subtype }
	| CONCAT { SSyntax.Concat }
	| AND { SSyntax.And }
	| OR { SSyntax.Or }
	| BITWISEAND { SSyntax.BitwiseAnd }
	| BITWISEOR { SSyntax.BitwiseOr}
	| BITWISEXOR { SSyntax.BitwiseXor }
	| LEFTSHIFT { SSyntax.LeftShift }
	| SIGNEDRIGHTSHIFT { SSyntax.SignedRightShift }
	| UNSIGNEDRIGHTSHIFT { SSyntax.UnsignedRightShift }
	| LCONS { SSyntax.LCons }
	| M_ATAN2 { SSyntax.M_atan2 }
	| M_POW {SSyntax.M_pow }
;

unop_target: 
	| NOT { SSyntax.Not }
	| MINUS { SSyntax.Negative }
	| TOSTRING { SSyntax.ToStringOp }
	| TONUMBER { SSyntax.ToNumberOp }
	| TOINT { SSyntax.ToIntOp }
	| TOUINT16 { SSyntax.ToUint16Op }
	| TOINT32 { SSyntax.ToInt32Op }
	| TOUINT32 { SSyntax.ToUint32Op }
	| BITWISENOT { SSyntax.BitwiseNot }
	| CAR { SSyntax.Car }
	| CDR { SSyntax.Cdr }
	| ISPRIMITIVE { SSyntax.IsPrimitive }
	| LENGTH { SSyntax.Length }
	| M_ABS   { SSyntax.M_abs }
	| M_ACOS  { SSyntax.M_acos }
	| M_ASIN  { SSyntax.M_asin }
	| M_ATAN  { SSyntax.M_atan }
	| M_CEIL  { SSyntax.M_ceil }
	| M_COS   { SSyntax.M_cos }
	| M_EXP   { SSyntax.M_exp }
	| M_FLOOR { SSyntax.M_floor }
	| M_LOG   { SSyntax.M_log }
	| M_ROUND { SSyntax.M_round }
	| M_SIN   { SSyntax.M_sin }
	| M_SQRT  { SSyntax.M_sqrt }
	| M_TAN   { SSyntax.M_tan }
;

call_with_target: 
	WITH; i=VAR { i }