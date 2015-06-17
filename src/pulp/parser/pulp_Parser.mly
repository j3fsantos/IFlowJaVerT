%{
open Pulp_Syntax
%}

%token <string> ID
%token <float> NUM
%token <string> STRING
%token LABEL
%token GOTO
%token SKIP
%token IF
%token THEN
%token ELSE
%token END
%token DEFEQ
%token LBRACKET
%token RBRACKET
%token LBRACE
%token RBRACE
%token TRUE
%token FALSE
%token NULL
%token UNDEFINED
%token EQUAL
%token LT
%token PLUS
%token MINUS
%token TIMES
%token DIV
%token MOD
%token AND
%token OR
%token BITWISE_AND
%token BITWISE_OR
%token BITWISE_XOR
%token LEFT_SHIFT
%token SIGNED_RIGHT_SHIFT
%token UNSIGNED_RIGHT_SHIFT
%token NOT
%token TO_STRING
%token TO_NUM
%token TO_INT32
%token TO_UINT32
%token BITWISE_NOT
%token SEMICOLON
%token COMMA
%token REF
%token FIELD
%token BASE
%token TYPEOF
%token MEM_REF
%token VAR_REF
%token EOF     

%start parse_pulp
%type <(Pulp_Syntax.statement list)> parse_pulp
%%

parse_pulp:
    prog=pulp EOF                               { prog }
;

pulp:
    seq=statement_seq                          { seq }
;

statement_seq:
    s=statement SEMICOLON seq=statement_seq   { s :: seq }
  | s=statement                               { [s] }
;

statement:
  | LABEL label=ID                         { Pulp_Syntax.Label label }
  | GOTO label=ID                          { Pulp_Syntax.Goto label }
  | GOTO LBRACKET e=expression RBRACKET ltrue=ID lfalse=ID   { Pulp_Syntax.GuardedGoto(e, ltrue, lfalse) }
  | SKIP                                   { Pulp_Syntax.Basic Pulp_Syntax.Skip }  (* TODO: does not work *)
  | v=var DEFEQ e=assign_right_expression  { Pulp_Syntax.Basic (Pulp_Syntax.Assignment { assign_left=v; assign_right=e }) }
  | LBRACKET o=expression COMMA f=expression RBRACKET DEFEQ e=expression { (Pulp_Syntax.Basic (Pulp_Syntax.Mutation (Pulp_Syntax.mk_mutation o f e))) }
  | IF c=expression THEN strue=statement_seq ELSE sfalse=statement_seq END { Pulp_Syntax.Sugar(Pulp_Syntax.If(c, strue, sfalse)) }
;

expression:
  | l=literal                               { Pulp_Syntax.Literal l }
  | v=ID                                    { Pulp_Syntax.Var v }
  | op=unaryOp e=expression                 { Pulp_Syntax.UnaryOp (op, e) }
  | e=expression op=binOp f=expression      { Pulp_Syntax.BinOp (e, op, f) }
  | LBRACE e=expression RBRACE              { e }
  | b=buildInFunc                           { b }
;

binOp:
  | op=comparisonOp                             { Comparison op }
  | op=arithOp                                  { Arith op } 
(*  | CONCAT                                      { Concat }    TODO: resolve naming conflict *) 
  | op=boolOp                                   { Boolean op }
  | op=bitwiseOp                                { Bitwise op }

comparisonOp:
  | EQUAL                                       { Equal }
  | LT                                          { LessThan }

arithOp:
  | PLUS                                        { Plus }
  | MINUS                                       { Minus }
  | TIMES                                       { Times }
  | DIV                                         { Div }
  | MOD                                         { Mod }

boolOp:
  | AND                                         { And }
  | OR                                          { Or }

bitwiseOp:
  | BITWISE_AND                                 { BitwiseAnd }
  | BITWISE_OR                                  { BitwiseOr }
  | BITWISE_XOR                                 { BitwiseXor }
  | LEFT_SHIFT                                  { LeftShift }
  | SIGNED_RIGHT_SHIFT                          { SignedRightShift }
  | UNSIGNED_RIGHT_SHIFT                        { UnsignedRightShift }

unaryOp:
  | NOT                                         { Not }
  | MINUS                                       { Negative }
  | TO_STRING                                   { ToStringOp }
  | TO_NUM                                      { ToNumberOp }
  | TO_INT32                                    { ToInt32Op }
  | TO_UINT32                                   { ToUint32Op }
  | BITWISE_NOT                                 { BitwiseNot }


literal:
  | NULL                                    { Null }
  | UNDEFINED                               { Undefined }
  | b=bool                                  { Bool b }
  | n=NUM                                   { Num n }
  | s=STRING                                { String s }
  (*TODO: add type literals*)
  (*TODO: add buildin locations *)

bool:
  | TRUE   { true }
  | FALSE  { false }

buildInFunc:
  | REF LBRACE e=expression COMMA f=expression COMMA t=reftype RBRACE  { Ref (e,f,t) }
  | FIELD LBRACE e=expression RBRACE        { Field e }
  | BASE LBRACE e=expression RBRACE         { Base e }
  | TYPEOF LBRACE e=expression RBRACE       { TypeOf e }

reftype:
  | MEM_REF { MemberReference }
  | VAR_REF { VariableReference }


assign_right_expression:
  e=expression                              { Pulp_Syntax.Expression e }
;

var:
  v=ID                                      { v }
;

