%token EOF

(* key words *)
%token TRUE
%token FALSE
%token WHILE
%token IF
%token ELSE
%token SKIP
%token NEW
%token DELETE
%token FUNCTION
%token RETURN
%token NULL

(* punctuation *)
%token COLON            /* : */
%token DOT              /* . */
%token SEMICOLON        /* ; */
%token COMMA            /* , */
%token ASSIGN           /* := */
%token RCBRACE          /* { */
%token LCBRACE          /* } */
%token LBRACE           /* ( */
%token RBRACE           /* ) */

%left SEMICOLON

(* names *)
%token <string> IDENTIFIER

(* values *)
%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token <string> LOCATION

(* Binary operators *)
%token EQUAL           /* = */
%token LESSTHAN        /* < */
%token GREATERTHAN     /* > */
%token LESSEQUAL       /* <= */
%token GREATEREQUAL    /* => */
%token PLUS            /* + */
%token MINUS           /* - */
%token TIMES           /* * */
%token DIV             /* / */
%token MOD             /* % */
%token AND             /* && */
%token OR              /* || */
%token NEQ             /* != */

(* Unary operators *)
%token NOT

(* WISL Program *)
%start <WISL_Syntax.program option> prog
%%

prog:
  | EOF { None }
  | fc = functions; stmt = statement; EOF { Some ({ WISL_Syntax.context=fc; WISL_Syntax.entry_point=(Some stmt) }) }
  | fc = functions; EOF { Some ({ WISL_Syntax.context = fc; WISL_Syntax.entry_point = None})}

functions:
  | (* empty *) { [] }
  | fdcl = functions; f = fct
    { f::fdcl }

fct:
  | FUNCTION; f = IDENTIFIER; LBRACE; params = var_list; RBRACE; LCBRACE; stmt = statement;
    SEMICOLON; RETURN; e = expression; RCBRACE;
    { (f, params, stmt, e) }


var_list:
  vl = separated_list(COMMA, IDENTIFIER) { vl }

statement:
  | SKIP { WISL_Syntax.Skip }
  | x = IDENTIFIER; ASSIGN; e = expression { WISL_Syntax.VarAssign (x, e) }
  | s1 = statement; SEMICOLON; s2 = statement { WISL_Syntax.Seq (s1, s2) } 
  | x = IDENTIFIER; ASSIGN; NEW; LBRACE; r = record; RBRACE
    { WISL_Syntax.New (x, r) }
  | DELETE; e = expression { WISL_Syntax.Delete e }
  | x = IDENTIFIER; ASSIGN; e = expression; DOT; pn = IDENTIFIER
    { WISL_Syntax.PropLookup (x, e, pn) }
  | e1 = expression; DOT; pn = IDENTIFIER; ASSIGN; e2 = expression
    { WISL_Syntax.PropUpdate (e1, pn, e2) }
  | x = IDENTIFIER; ASSIGN; f = IDENTIFIER; LBRACE; params = expr_list; RBRACE
    { WISL_Syntax.FunCall (x, f, params) }
  | WHILE; LBRACE; b = expression; RBRACE; LCBRACE; stmt = statement; RCBRACE
    { WISL_Syntax.While (b, stmt) }
  | IF; LBRACE; b = expression; RBRACE; LCBRACE; stmt1 = statement; RCBRACE;
    ELSE; LCBRACE; stmt2 = statement; RCBRACE
    { WISL_Syntax.If (b, stmt1, stmt2) }




record_field:
  pn = IDENTIFIER; COLON; e = expression { (pn, e) }

record:
  r = separated_list(COMMA, record_field) { r }

expr_list:
  el = separated_list(COMMA, expression) { el }

expression:
  | v = value { WISL_Syntax.Val v }
  | x = IDENTIFIER { WISL_Syntax.Var x }
  | e1 = expression; b = binop; e2 = expression { WISL_Syntax.BinOp (e1, b, e2) }
  | u = unop; e = expression { WISL_Syntax.UnOp (u, e) }

binop:
  | EQUAL { WISL_Syntax.EQUAL }
  | LESSTHAN { WISL_Syntax.LESSTHAN }
  | GREATERTHAN { WISL_Syntax.GREATERTHAN }
  | LESSEQUAL { WISL_Syntax.LESSEQUAL }
  | GREATEREQUAL { WISL_Syntax.GREATEREQUAL }
  | PLUS { WISL_Syntax.PLUS }
  | MINUS { WISL_Syntax.MINUS }
  | TIMES { WISL_Syntax.TIMES }
  | DIV { WISL_Syntax.DIV }
  | MOD { WISL_Syntax.MOD }
  | AND { WISL_Syntax.AND }
  | OR { WISL_Syntax.OR }
  | NEQ { WISL_Syntax.NEQ}

unop:
  | NOT { WISL_Syntax.NOT }
  
value:
  | i = INT { WISL_Syntax.Num (WISL_Syntax.Int i) }
  | f = FLOAT { WISL_Syntax.Num (WISL_Syntax.Float f) }
  | s = STRING { WISL_Syntax.Str s }
  | l = LOCATION { WISL_Syntax.Loc l }
  | TRUE { WISL_Syntax.Bool true }
  | FALSE { WISL_Syntax.Bool false }
  | NULL { WISL_Syntax.Null }


