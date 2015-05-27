%{
open Pulp_Syntax
%}

%token <string> ID
%token <float> NUM
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
%token SEMICOLON
%token COMMA
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
    v=ID                                    { Pulp_Syntax.Var v }
  | l=NUM                                   { Pulp_Syntax.Literal (Num l) }
;

assign_right_expression:
  e=expression                              { Pulp_Syntax.Expression e }
;

var:
  v=ID                                      { v }
;

