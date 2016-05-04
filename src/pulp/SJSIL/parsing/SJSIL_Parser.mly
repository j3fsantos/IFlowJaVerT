%{
open SSyntax 
%}

(* procedures *) 
%token PROC
%token RET
%token ERR
(*literals*)
%token <string> VAR
%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token <string> LOC
%token TRUE
%token FALSE
%token NULL 
%token UNDEFINED
%token EMPTY
(* Type literals *)
%token BOOLTYPELIT
%token NUMTYPELIT
%token STRTYPELIT
%token OBJTYPELIT
%token REFTYPELIT
%token VREFTYPELIT
%token OREFTYPELIT
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
%token LBRACE
%token RBRACE
%token LBRACKET
%token RBRACKET
%token CLBRACKET
%token CRBRACKET
(* main target *) 
%start <(SSyntax.procedure list)> prog_target
%%

prog_target:
	proc_list_target EOF	{ $1 }
;

proc_list_target: 
	proc_list = separated_list(SCOLON, proc_target) { proc_list };

proc_target: 
(* proc xpto (x, y) { cmd_list } with { ret: x, i; err: x, j }; *) 
	PROC; proc_name=VAR; LBRACE; param_list=param_list_target; RBRACE; CLBRACKET; cmd_list=cmd_list_target; CRBRACKET; WITH; CLBRACKET; ctx=ctx_target; CRBRACKET
	{
		let ret_var, ret_index, err_var, err_index = ctx in 
		{ 
    	SSyntax.proc_name = proc_name;
    	SSyntax.proc_body = cmd_list;
    	SSyntax.proc_params = param_list; 
			SSyntax.ret_label = ret_index;
			SSyntax.ret_var = ret_var;
			SSyntax.error_label = err_index;
			SSyntax.error_var = err_var
		}
	};

ctx_target: 
(* ret: x, i; err: x, j *)
	RET; COLON; ret_v=VAR; COMMA; i=INT; SCOLON; ERR; COLON; err_v=VAR; COMMA; j=INT
	{ ret_v, i, err_v, j }

param_list_target: 
	param_list = separated_list(COMMA, VAR) { param_list };

cmd_list_target: 
	cmd_list = separated_list(SCOLON, cmd_target) { cmd_list };

cmd_target: 
(* skip *)
	| SKIP 
		{ 
			Printf.printf "Parsing Skip.\n";
			SSyntax.SBasic(SSyntax.SSkip) 
		} 
(* x := new() *) 
	| v=VAR; DEFEQ; NEW; LBRACE; RBRACE
		{ 
			Printf.printf "Parsing New.\n";
			SSyntax.SBasic (SSyntax.SNew v) 
		}
(* x := e *)
	| v=VAR; DEFEQ; e=expr_target 
	{ 
		Printf.printf "Parsing Assignemnt.\n";
		SSyntax.SBasic (SSyntax.SAssignment (v, e)) 
	}
(* x := [e1, e2] *)
	| v=VAR; DEFEQ; LBRACKET; e1=expr_target; COMMA; e2=expr_target; RBRACKET 
		{ 
			Printf.printf "Parsing Field Look-up.\n";
			SSyntax.SBasic (SSyntax.SLookup (v, e1, e2)) 
		}
(* [e1, e2] := e3 *)
	| LBRACKET; e1=expr_target; COMMA; e2=expr_target; RBRACKET; DEFEQ; e3=expr_target    
		{ 
			Printf.printf "Parsing Field Assignemnt.\n";
			SSyntax.SBasic (SSyntax.SMutation (e1, e2, e3)) 
		}
(* delete(e1, e2) *)
	| DELETE; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
		{ 
			Printf.printf "Parsing Deletion.\n";
			SSyntax.SBasic (SSyntax.SDelete (e1, e2)) 
		}
(* x := hasField(e1, e2) *)
	| v=VAR; DEFEQ; HASFIELD; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
		{ 
			Printf.printf "Parsing HasField.\n";
			SSyntax.SBasic (SSyntax.SHasField (v, e1, e2)) 
		}
(* x := protoField(e1, e2) *)
	| v=VAR; DEFEQ; PROTOFIELD; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
		{ 
			Printf.printf "Parsing ProtoField.\n";
			SSyntax.SBasic (SSyntax.SProtoField (v, e1, e2)) 
		}
(* x := protoObj(e1, e2) *)
	| v=VAR; DEFEQ; PROTOOBJ; LBRACE; e1=expr_target; COMMA; e2=expr_target; RBRACE
		{ 
			Printf.printf "Parsing ProtoObj.\n";
			SSyntax.SBasic (SSyntax.SProtoObj (v, e1, e2)) 
		}
(* goto i *)
	| GOTO; i=INT 
		{
			Printf.printf "Parsing Goto.\n";
			SSyntax.SGoto i
		}
(* goto [e] i j *)
	| GOTO LBRACKET; e=expr_target; RBRACKET; i=INT; j=INT 
		{
			Printf.printf "Parsing Conditional Goto.\n";
			SSyntax.SGuardedGoto (e, i, j) 
		}
(* x := e(e1, ..., en) with j *)
	| v=VAR; DEFEQ; e=expr_target; LBRACE; es=expr_list_target; RBRACE; WITH; i=INT
		{
			Printf.printf "Parsing Procedure Call.\n";
			SSyntax.SCall (v, e, es, i) 
		}
;

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
		{ SSyntax.Base (e) }		
(* typeof *)
	| TYPEOF; LBRACE; e=expr_target; RBRACE
		{ SSyntax.TypeOf (e) }
;

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




