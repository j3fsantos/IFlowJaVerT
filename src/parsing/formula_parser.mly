%{
  open Logic
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
%left STAR PLUS MINUS       
%token EOF     
%start main            
%type <Logic.formula> main
%%
main:
    formula EOF                { $1 }
;

formula:
    formula STAR formula                                   { Star [$1; $3] }
  | LPAREN location COMMA ID RPAREN POINTSTO logical_expr { Heaplet ($2, $4, $7) }
  | LPAREN location COMMA ID RPAREN POINTSTO EMPTY        { HeapletEmpty ($2, $4) }
;

location:
    LG    { Lg }
  | LOP   { Lop }
  | LFP   { Lfp }
  | LOC   { LocNum $1 }
  | AHLOC { AbsLoc {lid = $1; ltype = LocAh} }
  | PLLOC { AbsLoc {lid = $1; ltype = LocApl} }
  | STORELOC { AbsLoc {lid = $1; ltype = LocS} }
;

location_b:
  | location { Lb_Loc $1 }
  | LOC_NULL { Lb_LocNull }

logical_bin_op:
  PLUS { Lbo_plus }

logical_expr :
  LE_VAR { Le_Var $1 }
  | NUM { pv_le (Pv_Num $1) }
  | STRING { pv_le (Pv_String $1) }
  | UNDEFINED { pv_le Pv_Undefined }
  | NULL { pv_le Pv_Null }
  | TRUE { pv_le (Pv_Bool true) }
  | FALSE { pv_le (Pv_Bool false) }
  | location_b {lb_le $1}
  | logical_expr logical_bin_op logical_expr {Le_BinOp ($1, $2, $3) }
  | location_b DOT ID { Le_Ref ($1, $3) }
;

