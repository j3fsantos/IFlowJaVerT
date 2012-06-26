%{
  open List
  open Logic  
  
  let get_fields xs xvs = 
    {
      has = List.fold_left (fun l (x, v) -> EFields.add x v l) EFields.empty xvs; 
      hasnt = xs 
    }
    
	let parse_error s =
	  let start_pos = Parsing.symbol_start () in
	  let end_pos = Parsing.symbol_end () in
	  Printf.printf "Error between %d and %d\n%s\n" start_pos end_pos s
    
  let make_heaplets l hasnt has =
    Star ( (map (fun x -> HeapletEmpty (l, x)) hasnt) @ (map (fun (x, v) -> Heaplet (l, x, v)) has)  )

%}

%token STAR
%token LPAREN
%token RPAREN
%token POINTSTO
%token EMPTY
%token <string> ID 
%token EQ
%token NEQ
%token LE
%token LT
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
%token OBJECT
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
%token <Logic.logical_var> LOC
%token <Logic.logical_var> AHLOC
%token <Logic.logical_var> PLLOC
%token <Logic.logical_var> STORELOC
%token LOC_NULL
%token PLUS MINUS 
%token <Logic.logical_var> LE_VAR
%token RETURN
%token CSCOPE
%token AHEAPLETS
%token PLIST
%token STORE
%token FUN
%token <Logic.pname> PNAME
%token DEFEQ
%token DEFINE
%left STAR PLUS MINUS       
%token EOF     
%start main            
%type <Logic.annot_body> main
%%
main:
    formula EOF                { ABFormula $1 }
  | defn_list EOF                   { ABPredDefn $1 }
;

defn:
    DEFINE PNAME LPAREN logical_var_list RPAREN DEFEQ defn_body SEMICOLON  { { name = $2; args = $4; rhss = $7 } }
;

defn_list:
    defn defn_list     { $1 :: $2 }
  | defn               { [$1] }

defn_body:
    formula VBAR defn_body     { $1 :: $3 }
  | formula                  { [$1] }


formula:
    formula STAR formula                                 { Star [$1; $3] }
  | LPAREN location COMMA ID RPAREN POINTSTO logical_exp { Heaplet ($2, $4, $7) }
  | LPAREN location COMMA ID RPAREN POINTSTO EMPTY       { HeapletEmpty ($2, $4) }
  | logical_exp EQ logical_exp                           { Eq ($1, $3) }
  | logical_exp NEQ logical_exp                          { NEq ($1, $3) }
  | logical_exp LE logical_exp                           { IsTrue (Le_BinOp ($1, Lbo_le, $3)) }
  | logical_exp LT logical_exp                           { IsTrue (Le_BinOp ($1, Lbo_lt, $3)) }
  | RETURN EQ logical_exp                                { REq $3 }
  | PNAME LPAREN logical_exp_list RPAREN                 { UDPred ($1, $3) }
  | ISTRUE LPAREN logical_exp RPAREN                     { IsTrue $3 }
  | ISFALSE LPAREN logical_exp RPAREN                    { IsFalse $3 }
  | CSCOPE EQ LBRACKET location_list RBRACKET            { CScopes $4 }
  | AHEAPLETS LBRACKET location RBRACKET LPAREN id_list VBAR id_value_list RPAREN 
    { Storelet ({
      stl_loc_f = $3;
      stl_loc_s = Lb_LocNull;
      stl_tail = Some Lb_LocNull;
      stl_fp_fields = get_fields $6 $8;
      stl_sp_fields = empty_fields
    }) }
  | AHEAPLETS LBRACKET location COMMA location_b COMMA location_b RBRACKET 
    LPAREN id_list VBAR id_value_list RPAREN 
    LPAREN id_list VBAR id_value_list RPAREN
    { Storelet ({
      stl_loc_f = $3;
      stl_loc_s = $7;
      stl_tail = Some $5;
      stl_fp_fields = get_fields $10 $12;
      stl_sp_fields = get_fields $15 $17
    }) }
	| PLIST LBRACKET location COMMA location_b RBRACKET LPAREN id_list VBAR id_value_list RPAREN
		{ PList ({
		  pl_id = $3;
      pl_tail = Some $5;  
		  pl_fields = get_fields $8 $10 
		}) }
  | OBJFOOTPRINT LBRACKET location RBRACKET LPAREN id_list RPAREN { ObjFootprint ($3, $6) }
	| STORE LBRACKET location RBRACKET LPAREN id_list VBAR id_value_list RPAREN
    { Store ({
      s_id = $3;
      s_fields = get_fields $6 $8
    }) }
  | OBJECT LBRACKET location RBRACKET LPAREN id_list VBAR id_value_list RPAREN 
    { make_heaplets $3 $6 $8  }
;

location:
    LG       { Lg }
  | LOP      { Lop }
  | LFP      { Lfp }
  | LOC      { LocNum $1 }
  | AHLOC    { AbsLoc {lid = $1; ltype = LocStl} }
  | PLLOC    { AbsLoc {lid = $1; ltype = LocPl} }
  | STORELOC { AbsLoc {lid = $1; ltype = LocS} }
;

location_b:
    location { Lb_Loc $1 }
  | LOC_NULL { Lb_LocNull }

logical_bin_op:
  PLUS { Lbo_plus }
  
location_list:
    location SEMICOLON location_list { $1 :: $3 }
  | location                         { [$1] }
  | /*empty*/                        { [] } 

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
  | FUN LPAREN id_list RPAREN ID           { Le_FunC ($3, $5) }
   /* Do not have function expression for now */

logical_exp_list:
    logical_exp COMMA logical_exp_list     { $1 :: $3 }
  | logical_exp                            { [$1] }
  | /*empty*/                              { [] } 


logical_var_list:
    LE_VAR COMMA logical_var_list          { $1 :: $3 }
  | LE_VAR                                 { [$1] }
  | /*empty*/                              { [] } 


id_list :
    ID COMMA id_list { $1 :: $3 }
  | ID               { [$1] } 
  | /*empty*/        { [] }

id_value :
  ID COLON logical_exp { ($1, $3) }

id_value_list :
    id_value COMMA id_value_list { $1 :: $3 }
  | id_value                     { [$1] }
  | /*empty*/                    { [] }
;

