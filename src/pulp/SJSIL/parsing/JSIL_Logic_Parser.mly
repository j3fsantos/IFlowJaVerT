%{
open SSyntax 
open JSIL_Logic_Syntax
%}

(* procedures *) 
%token SPEC
%token NORMAL
%token ERR
%token PRE
%token POST
%token FLAG
(*literals*)
%token <string> LVAR
%token <string> PVAR
%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token <string> LOC
%token TRUE
%token FALSE
%token NULL 
%token UNDEFINED
%token EMPTY
%token LNONE
(* Type literals *)
%token BOOLTYPELIT
%token NUMTYPELIT
%token STRTYPELIT
%token OBJTYPELIT
%token REFTYPELIT
%token VREFTYPELIT
%token OREFTYPELIT
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
%token LCONS
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
(* unary operators *)
%token NOT
%token TOSTRING
%token TONUMBER
%token TOINT32
%token TOUINT32
%token BITWISENOT
(* separators *)
%token EOF
%token COMMA
%token COLON
%token SCOLON
%token DOT
%token LBRACE
%token RBRACE
%token LBRACKET
%token RBRACKET
(* main target *) 
%start <(JSIL_Logic_Syntax.jsil_spec list)> main_target
%%

main_target:
	spec_list_target EOF	{ $1 }
;

spec_list_target: 
	spec_list = separated_list(SCOLON, spec_target) { spec_list };

spec_target: 
(* spec xpto (x, y) pre: assertion, post: assertion, flag: NORMAL|ERROR *) 
	SPEC; proc_name=PVAR; LBRACE; param_list=param_list_target; RBRACE; pre_post_list=pre_post_list_target
	{ 
		{ 
    	spec_name = proc_name;
    	spec_params = param_list;
			proc_specs = pre_post_list 
		}
	};
	
pre_post_list_target:
	pre_post_list = separated_list(COMMA, pre_post_target) { pre_post_list };

pre_post_target:
	PRE; COLON; pre_assertion=assertion_target; COMMA; POST; COLON; post_assertion=assertion_target; COMMA; FLAG; COLON; ret_flag=ret_flag_target
	{
		Printf.printf "I am processing a pre_post_target\n"; 
		{
			pre = pre_assertion;
			post = post_assertion;
			ret_flag = ret_flag
		}
	};

ret_flag_target: 
	| NORMAL { Normal }
	| ERR { Error }
; 

param_list_target: 
	param_list = separated_list(COMMA, PVAR) { param_list };

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
			Printf.printf "I got a star assertion \n";
			LStar (left_ass, right_ass) 
		}
(* (E, E) -> E *)
	| LBRACE; obj_expr=lexpr_target; COMMA; prop_expr=lexpr_target; RBRACE; LARROW; val_expr=lexpr_target
		{ 
			Printf.printf "I got a cell assertion \n"; 
			LPointTo (obj_expr, prop_expr, val_expr) 
		}
(* emp *)
	| LEMP;
		{ 
			Printf.printf "I got the assertion: emp\n"; 
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
(* lval *)
	| value=lval_target { LVal value }
(* lvar *)
	| v=LVAR { LVar v }
(* pvar *)
	| v=PVAR { PVar v }
(* binop *)	
	| e1=lexpr_target; bop=binop_target; e2=lexpr_target { LBinOp (e1, bop, e2) }
(* unop *)
  | uop=unop_target; e=lexpr_target { LUnOp (uop, e) }
(* vref *)
	| VREF; LBRACE; e1=lexpr_target; COMMA; e2=lexpr_target; RBRACE
		{ LVRef (e1, e2) }
(* oref *)
	| OREF; LBRACE; e1=lexpr_target; COMMA; e2=lexpr_target; RBRACE
		{ LORef (e1, e2) }
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
		{ LCons (e1, e2) }
(* (e) *)
  | LBRACE; e=lexpr_target; RBRACE
	  { e }
;

lval_target:
(* literal *)
	| lit=lit_target
		{ LLit lit }
(* none *)
	| LNONE
		{ LNone }
(* [] *)
	| LBRACKET; RBRACKET
		{ LListEmpty }

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
	| TRUE { SSyntax.Bool true }
	| FALSE { SSyntax.Bool false }
	| i=INT { SSyntax.Num (float_of_int i) }
	| x=FLOAT { SSyntax.Num x }
	| s=STRING { SSyntax.String s }
	| loc=LOC { SSyntax.Loc loc }
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
;

unop_target: 
	| NOT { SSyntax.Not }
	| MINUS { SSyntax.Negative }
	| TOSTRING { SSyntax.ToStringOp }
	| TONUMBER { SSyntax.ToNumberOp }
	| TOINT32 { SSyntax.ToInt32Op }
	| TOUINT32 { SSyntax.ToUint32Op }
	| BITWISENOT { SSyntax.BitwiseNot }
;




