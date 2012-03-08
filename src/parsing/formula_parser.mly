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
%token PLUS MINUS 
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
;

logical_expr :
  NUM { pv_le (Pv_Num $1) }
;

