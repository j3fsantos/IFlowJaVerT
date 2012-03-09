%{
  open Logic
  
  let get_fields xs xvs = 
    {
      has = List.fold_left (fun l (x, v) -> EFields.add x v l) EFields.empty xvs; 
      hasnt = xs 
    }
%}

%token STAR
%token LPAREN
%token RPAREN
%token POINTSTO
%token EMPTY
%token <string> ID 
%token EQ
%token NEQ
%token ISTRUE
%token ISFALSE
%token CSCOPES
%token LBRACKET
%token RBRACKET
%token COMMA
%token COLON
%token SEMICOLON
%token DOT
%token VBAR
%token AHEAPLETS 
%token APLIST
%token OBJFOOTPRINT
%token STORE
%token <int> NUM
%token <string> STRING
%token UNDEFINED
%token NULL
%token TRUE
%token FALSE
%token LG
%token LOP
%token LFP
%token <int> LOC
%token <int> AHLOC
%token <int> PLLOC
%token <int> STORELOC
%token LOC_NULL
%token PLUS MINUS 
%token <string> LE_VAR
%token RETURN
%token CSCOPE
%token AHEAPLETS
%token PLIST
%token STORE
%left STAR PLUS MINUS       
%token EOF     
%start main            
%type <Logic.formula> main
%%
main:
    formula EOF                { $1 }
;

formula:
    formula STAR formula                                 { Star [$1; $3] }
  | LPAREN location COMMA ID RPAREN POINTSTO logical_exp { Heaplet ($2, $4, $7) }
  | LPAREN location COMMA ID RPAREN POINTSTO EMPTY       { HeapletEmpty ($2, $4) }
  | logical_exp EQ logical_exp                           { Eq ($1, $3) }
  | logical_exp NEQ logical_exp                          { NEq ($1, $3) }
  | RETURN EQ logical_exp                                { REq $3 }
  | ISTRUE LPAREN logical_exp RPAREN                     { IsTrue $3 }
  | ISFALSE LPAREN logical_exp RPAREN                    { IsFalse $3 }
  | CSCOPE EQ LBRACKET location_list RBRACKET            { CScopes $4 }
  | AHEAPLETS LBRACKET location RBRACKET LPAREN id_list VBAR id_value_list RPAREN 
    { AbstractHeaplets ({
      ah_loc = $3; 
      ah_fields = get_fields $6 $8
    }) }
	| PLIST LBRACKET location COMMA location_b RBRACKET LPAREN id_list VBAR id_value_list RPAREN
		{ AbstractProtoList ({
		  pl_id = $3;
      pl_tail = $5;  
		  pl_fields = get_fields $8 $10 
		}) }
  | OBJFOOTPRINT LPAREN location SEMICOLON id_list RPAREN { ObjFootprint ($3, $5) }
	| STORE LBRACKET location RBRACKET LPAREN id_list VBAR id_value_list RPAREN
    { Store ({
      s_id = $3;
      s_fields = get_fields $6 $8
    }) }
;

location:
    LG       { Lg }
  | LOP      { Lop }
  | LFP      { Lfp }
  | LOC      { LocNum $1 }
  | AHLOC    { AbsLoc {lid = $1; ltype = LocAh} }
  | PLLOC    { AbsLoc {lid = $1; ltype = LocApl} }
  | STORELOC { AbsLoc {lid = $1; ltype = LocS} }
;

location_b:
    location { Lb_Loc $1 }
  | LOC_NULL { Lb_LocNull }

logical_bin_op:
  PLUS { Lbo_plus }
  
location_list:
    location location_list { $1 :: $2 }
  | /*empty*/              { [] } 

logical_exp :
    LE_VAR                                 { Le_Var $1 }
  | NUM                                    { pv_le (Pv_Num $1) }
  | STRING                                 { pv_le (Pv_String $1) }
  | UNDEFINED                              { pv_le Pv_Undefined }
  | NULL                                   { pv_le Pv_Null }
  | TRUE                                   { pv_le (Pv_Bool true) }
  | FALSE                                  { pv_le (Pv_Bool false) }
  | location_b                             { lb_le $1 }
  | LPAREN logical_exp logical_bin_op logical_exp RPAREN { Le_BinOp ($2, $3, $4) }
  | location_b DOT ID                      { Le_Ref ($1, $3) }
  | LBRACKET location_list RBRACKET        { Le_Scope $2 }
  /* Do not have function expression for now */
  
id_list :
    ID COMMA id_list { $1 :: $3 }
  | /*empty*/  { [] }

id_value :
  ID COLON logical_exp { ($1, $3) }

id_value_list :
    id_value COMMA id_value_list { $1 :: $3 }
  | /*empty*/  { [] }
;

