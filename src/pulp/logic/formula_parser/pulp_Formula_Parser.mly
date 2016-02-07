/* ./src/pulp/logic/formula_parser/pulp_Formula_Parser.mly
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 */

%{
  open List
  open Pulp_Logic
  open Pulp_Syntax
    
    let parse_error s =
      let start_pos = Parsing.symbol_start () in
      let end_pos = Parsing.symbol_end () in
      Printf.printf "Error between %d and %d\n%s\n" start_pos end_pos s
    
  let make_heaplets l hasnt has =
    Star ( (map (fun x -> Heaplet (l, x, Le_None)) hasnt) @ (map (fun (x, v) -> Heaplet (l, x, v)) has)  )

%}

%token STAR
%token LPAREN
%token RPAREN
%token POINTSTO
%token <string> ID 
%token EQ
%token NEQ
%token LE
%token LT
%token LBRACKET
%token RBRACKET
%token COMMA
%token COLON
%token SEMICOLON
%token DOT
%token VBAR
%token OR
%token OBJFOOTPRINT
%token OBJECT
%token PROTO_VALUE
%token PROTO_CHAIN
%token PROTO_PRED
%token <float> NUM
%token <string> STRING
%token UNDEFINED
%token EMPTY
%token NONE
%token NULLTYPE
%token UNDEFINEDTYPE
%token BOOLEANTYPE
%token STRINGTYPE
%token NUMBERTYPE
%token OBJECTTYPE
%token OBJECTTYPENORMAL
%token OBJECTTYPEBUILTIN
%token REFERENCETYPE
%token VREFERENCETYPE
%token OREFERENCETYPE
%token NULL
%token TRUE
%token FALSE
%token LG
%token LOBJECT
%token LBOOLEAN
%token LSTRING
%token LOP
%token LFP
%token LREP
%token LTEP
%token REF
%token VREF
%token OREF
%token BASE
%token FIELD
%token TYPEOF
%token NOT
%token PLUS MINUS CONCAT 
%token <Pulp_Logic.logical_var> LE_VAR
%token RETURN
%left STAR PLUS MINUS       
%token EOF     
%start main            
%type <Pulp_Logic.annot_body> main
%%
main:
    formula EOF            { $1 }
;

disj_of_formulas:
    formula OR disj_of_formulas     { $1 :: $3 }
  | formula                  { [$1] }


formula:
    formula STAR formula                                 { Star [$1; $3] }
  | LPAREN logical_exp COMMA logical_exp RPAREN POINTSTO logical_exp { Heaplet ($2, $4, $7) }
  | logical_exp EQ logical_exp                           { Eq ($1, $3) }
  | logical_exp NEQ logical_exp                          { NEq ($1, $3) }
  | RETURN EQ logical_exp                                { REq $3 }
  | OBJFOOTPRINT LBRACKET logical_exp RBRACKET LPAREN logical_exp_list RPAREN { ObjFootprint ($3, $6) }
  | OBJECT LBRACKET logical_exp RBRACKET LPAREN logical_exp_list VBAR logical_exp_value_list RPAREN 
    { make_heaplets $3 $6 $8  }
  | PROTO_VALUE LPAREN logical_exp COMMA logical_exp COMMA logical_exp COMMA logical_exp COMMA logical_exp RPAREN 
    { Pi (mk_pi_pred $3 $5 $7 $9 $11) }
  | PROTO_CHAIN LPAREN logical_exp COMMA logical_exp COMMA logical_exp RPAREN 
    { ProtoChain ($3, $5, $7) }
  | PROTO_PRED LPAREN logical_exp COMMA logical_exp COMMA logical_exp COMMA logical_exp COMMA logical_exp RPAREN 
    { proto_pred_f $3 $5 $7 $9 $11 } 
;

/* TODO */
location:
    LG       { Lg }
  | LOP      { Lop }
  | LFP      { Lfp }
  | LREP     { Lrep }
  | LTEP     { Ltep }
  | LOBJECT    { LObject }
  | LBOOLEAN   { LBoolean }
  | LSTRING    { LString }
;

logical_bin_op:
    PLUS { Arith Plus }
  | MINUS { Arith Minus }
  | CONCAT { Concat } 
  | LT { Comparison LessThan }
  
logical_unary_op:
  NOT { Not }
  
pulp_type:
    NULLTYPE            { NullType }
  | UNDEFINEDTYPE       { UndefinedType }
  | BOOLEANTYPE         { BooleanType }
  | STRINGTYPE          { StringType }
  | NUMBERTYPE          { NumberType }
  | OBJECTTYPE          { ObjectType None }
  | OBJECTTYPENORMAL    { ObjectType (Some Normal) }
  | OBJECTTYPEBUILTIN   { ObjectType (Some Builtin) }
  | REFERENCETYPE       { ReferenceType None }
  | VREFERENCETYPE      { ReferenceType (Some VariableReference) }
  | OREFERENCETYPE      { ReferenceType (Some MemberReference) }

reference_type:
    VREF                { VariableReference }
  | OREF                { MemberReference }

literal :
    location { LLoc $1 }
  | NULL                                   { Null }   
  | TRUE                                   { Bool true }
  | FALSE                                  { Bool false }    
  | NUM                                    { Num $1 }   
  | STRING                                 { String $1 }                
  | UNDEFINED                              { Undefined }
  | pulp_type                              { Type $1 }    
  | EMPTY                                  { Empty } 

logical_exp :
    LE_VAR                                                          { Le_Var $1 }
  | NONE                                                            { Le_None }
  | ID                                                              { Le_PVar $1 } 
  | literal                                                         { Le_Literal $1 }
  | LPAREN logical_unary_op logical_exp RPAREN                      { Le_UnOp ( $2, $3) }
  | LPAREN logical_exp logical_bin_op logical_exp RPAREN            { Le_BinOp ($2, $3, $4) }
  | REF LPAREN logical_exp COMMA logical_exp COMMA reference_type   { Le_Ref ($3, $5, $7) }
  | BASE LPAREN logical_exp RPAREN                                  { Le_Base ($3) }
  | FIELD LPAREN logical_exp RPAREN                                 { Le_Field ($3) }
  | TYPEOF LPAREN logical_exp RPAREN                                { Le_TypeOf ($3) }

logical_exp_list:
    logical_exp COMMA logical_exp_list     { $1 :: $3 }
  | logical_exp                            { [$1] }
  | /*empty*/                              { [] } 

logical_exp_value :
  logical_exp COLON logical_exp { ($1, $3) }

logical_exp_value_list :
    logical_exp_value COMMA logical_exp_value_list { $1 :: $3 }
  | logical_exp_value                              { [$1] }
  | /*empty*/                                      { [] }
;

