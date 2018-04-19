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
%token PREDICATE
%token INVARIANT
%token FOLD
%token UNFOLD
%token APPLY
%token RECUNFOLD
%token ASSERT
%token PRE
%token POST
%token VARIANT
%token HYPOTHESIS
%token CONCLUSIONS
%token PROOF
%token LEMMA


(* punctuation *)
%token COLON            /* : */
%token DOT              /* . */
%token SEMICOLON        /* ; */
%token COMMA            /* , */
%token ASSIGN           /* := */
%token RCBRACE          /* } */
%token LCBRACE          /* { */
%token LBRACE           /* ( */
%token RBRACE           /* ) */
%token LBRACK           /* [ */
%token RBRACK           /* ] */


%right  SEMICOLON         /* ; */

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
%token LSTCONS         /* :: */
%token LSTCAT          /* @ */

(* Unary operators *)
%token NOT
%token HEAD
%token TAIL
%token LEN

(* Logic *)
%token ARROW          /* -> */
%token EMP
%token LAND           /* /\ */
%token LOR            /* \/ */
%token LEQ            /* == */
%token LLESS           /* <#  */
%token LLESSEQ         /* <=# */
%token LGREATER        /* >#  */
%token LGREATEREQ      /* >=# */
%token LTRUE
%token LFALSE
%token LSTNIL
%token LNOT
%token <string> LVAR

(* Reserved names *)
%token XRET

(* WISL Program *)
%start <WISL_Syntax.program option> prog
%%

prog:
  | EOF { None }
  | fcp = definitions; stmts = statement_with_meta_list; EOF { 
    let (fc, preds, lemmas) = fcp in
    Some (WISL_Syntax.{ lemmas = lemmas; predicates = preds; context=fc; entry_point=(Some stmts) })
  }
  | fcp = definitions; EOF {
    let (fc, preds, lemmas) = fcp in
    Some (WISL_Syntax.{ lemmas = lemmas; predicates = preds; context = fc; WISL_Syntax.entry_point = None })}

definitions:
  | (* empty *) { ([], [], []) }
  | fpdcl = definitions; p = predicate
    { let (fs, ps,ls) = fpdcl in
      (fs, p::ps, ls) }
  | fpdcl = definitions; l = lemma
    { let (fs, ps, ls) = fpdcl in
      (fs, ps, l::ls) }
  | fpdcl = definitions; f = fct
    { let (fs, ps, ls) = fpdcl in
      (f::fs, ps, ls) }


fct:
  | LCBRACE; pre = logic_assertion; RCBRACE; f = fct_only; LCBRACE;
  post = logic_assertion; RCBRACE { WISL_Utils.add_spec f pre post }
  | f = fct_only { f }

fct_only:
  | FUNCTION; f = IDENTIFIER; LBRACE; params = var_list; RBRACE; LCBRACE;
    stmtsandret = statement_with_meta_list_and_return; RCBRACE;
    { let (stmts, e) = stmtsandret in 
      WISL_Syntax.{name=f; params=params; body=stmts; return_expr=e; spec=None} }


var_list:
  vl = separated_list(COMMA, IDENTIFIER) { vl }


statement_with_meta_list_and_return:
  | RETURN; e = expression { ([], e)  }
  | sm = statement_with_meta; SEMICOLON; sle = statement_with_meta_list_and_return
    { let (sl, e) = sle in (sm::sl, e) }

statement_with_meta_list:
  | sl = separated_nonempty_list(SEMICOLON, statement_with_meta) { sl }

statement_with_meta:
  | inv = option(invariant); 
    pre = option(pre_logic_cmds);
    s = statement;
    post = option(post_logic_cmds)
    { 
      let prec = Option.map_default (fun x -> x) [] pre in
      let postc = Option.map_default (fun x -> x) [] post in
      let metadata = WISL_Syntax.{invariant = inv; precmds = prec; postcmds = postc; } in
      (metadata, s) }

invariant:
  | INVARIANT; l = logic_assertion ; RCBRACE { l }

pre_logic_cmds:
  | PRE; lcmds = separated_list(SEMICOLON, logic_command); RCBRACE { lcmds }
post_logic_cmds:
  | POST; lcmds = separated_list(SEMICOLON, logic_command); RCBRACE { lcmds }

statement:
  | SKIP { WISL_Syntax.Skip }
  | x = IDENTIFIER; ASSIGN; e = expression { WISL_Syntax.VarAssign (x, e) }
  | x = IDENTIFIER; ASSIGN; NEW; LBRACE; r = record; RBRACE
    { WISL_Syntax.New (x, r) }
  | DELETE; e = expression { WISL_Syntax.Delete e }
  | x = IDENTIFIER; ASSIGN; e = expression; DOT; pn = IDENTIFIER
    { WISL_Syntax.PropLookup (x, e, pn) }
  | e1 = expression; DOT; pn = IDENTIFIER; ASSIGN; e2 = expression
    { WISL_Syntax.PropUpdate (e1, pn, e2) }
  | x = IDENTIFIER; ASSIGN; f = IDENTIFIER; LBRACE; params = expr_list; RBRACE
    { WISL_Syntax.FunCall (x, f, params) }
  | WHILE; LBRACE; b = expression; RBRACE; LCBRACE; sl = statement_with_meta_list; RCBRACE
    { WISL_Syntax.While (b, sl) }
  | IF; LBRACE; b = expression; RBRACE; LCBRACE; sl1 = statement_with_meta_list; RCBRACE;
    ELSE; LCBRACE; sl2 = statement_with_meta_list; RCBRACE
    { WISL_Syntax.If (b, sl1, sl2) }


record_field:
  pn = IDENTIFIER; COLON; e = expression { (pn, e) }

record:
  r = separated_list(COMMA, record_field) { r }

expr_list:
  el = separated_list(COMMA, expression) { el }

expression:
  | LBRACE; e = expression; RBRACE { e }
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
  | LEN { WISL_Syntax.LEN }
  | HEAD { WISL_Syntax.HEAD }
  | TAIL { WISL_Syntax.TAIL }
  
value:
  | i = INT { WISL_Syntax.Num (WISL_Syntax.Int i) }
  | f = FLOAT { WISL_Syntax.Num (WISL_Syntax.Float f) }
  | s = STRING { WISL_Syntax.Str s }
  | l = LOCATION { WISL_Syntax.Loc l }
  | LBRACK; vl = separated_list(COMMA, value); RBRACK { WISL_Syntax.VList vl }
  | TRUE { WISL_Syntax.Bool true }
  | FALSE { WISL_Syntax.Bool false }
  | NULL { WISL_Syntax.Null }


(* Logic stuff *)

lemma:
  | LEMMA; name = IDENTIFIER; LBRACE; params = var_list; RBRACE; LCBRACE;
    vari = option(variant_def); hypo = hypo_def; concls = concls_def;
    proof = option(proof_def); RCBRACE
    { WISL_Syntax.{ lemma_name = name; lemma_params = params; proof = proof;
      variant = vari; hypothesis = hypo; conclusions = concls } }

variant_def:
  | VARIANT; COLON; e = expression { e }

hypo_def:
  | HYPOTHESIS; COLON; la = logic_assertion { la }

concls_def:
  | CONCLUSIONS; COLON; las = separated_nonempty_list(SEMICOLON, logic_assertion)
    { las }

proof_def:
  | PROOF; COLON; pr = separated_nonempty_list(SEMICOLON, logic_command)
    { pr }

predicate:
  | PREDICATE; p = IDENTIFIER; LBRACE; params = var_list; RBRACE; LCBRACE;
    defs = separated_nonempty_list(SEMICOLON, named_logic_assertion); RCBRACE;
    { WISL_Syntax.{pred_name=p; pred_params=params; pred_definitions=defs} }

named_logic_assertion:
  | id = option(assertion_id); a = logic_assertion
    { (id, a) }
    
assertion_id:
  | LBRACK; n = IDENTIFIER; RBRACK { n }


logic_command:
  | FOLD; a = logic_assertion { WISL_Syntax.Fold a }
  | UNFOLD; a = logic_assertion { WISL_Syntax.Unfold a }
  | APPLY; name = IDENTIFIER; LBRACE;
    params = separated_list(COMMA, logic_expression); RBRACE
    { WISL_Syntax.ApplyLem (name, params) }
  | RECUNFOLD; x = IDENTIFIER { WISL_Syntax.RecUnfold x }
  | IF; LBRACE; g = logic_expression; RBRACE; LCBRACE;
    thencmds = separated_list(SEMICOLON, logic_command); RCBRACE;
    ELSE; LCBRACE; elsecmds = separated_list(SEMICOLON, logic_command); RCBRACE
    { WISL_Syntax.LogicIf (g, thencmds, elsecmds) }
  | IF; LBRACE; g = logic_expression; RBRACE; LCBRACE;
    thencmds = separated_list(SEMICOLON, logic_command); RCBRACE;
    { WISL_Syntax.LogicIf (g, thencmds, [])}
  | ASSERT; a = logic_assertion { WISL_Syntax.Assert a }


logic_assertion:
  | LBRACE; la = logic_assertion; RBRACE; { la }
  | LTRUE { WISL_Syntax.LTrue }
  | LFALSE { WISL_Syntax.LFalse }
  | pr = IDENTIFIER; LBRACE; params = separated_list(COMMA, logic_expression); RBRACE
    { WISL_Syntax.LPred (pr, params) }
  | LNOT; la = logic_assertion { WISL_Syntax.LNot la }
  | la1 = logic_assertion; LAND; la2 = logic_assertion { WISL_Syntax.LAnd (la1, la2) }
  | la1 = logic_assertion; LOR; la2 = logic_assertion { WISL_Syntax.LOr (la1, la2) }
  | EMP { WISL_Syntax.LEmp }
  | la1 = logic_assertion; TIMES; la2 = logic_assertion { WISL_Syntax.LStar (la1, la2) }
  | LBRACE; le1 = logic_expression; COMMA; pn = IDENTIFIER; RBRACE; ARROW;
    le3 = logic_expression { WISL_Syntax.LPointsTo (le1, pn, le3) }
  | le1 = logic_expression; LEQ; le2 = logic_expression { WISL_Syntax.LEq (le1, le2) }
  | le1 = logic_expression; LLESS; le2 = logic_expression { WISL_Syntax.LLess (le1, le2) }
  | le1 = logic_expression; LLESSEQ; le2 = logic_expression { WISL_Syntax.LLessEq (le1, le2) }
  | le1 = logic_expression; LGREATEREQ; le2 = logic_expression { WISL_Syntax.LGreaterEq (le1, le2) }
  | le1 = logic_expression; LGREATER; le2 = logic_expression { WISL_Syntax.LGreater (le1, le2) }
  
logic_expression:
  | LBRACE; le = logic_expression; RBRACE { le }
  | v = logic_value { WISL_Syntax.LVal v }
  | x = IDENTIFIER { WISL_Syntax.PVar x }
  | lx = LVAR { WISL_Syntax.LVar lx }
  | e1 = logic_expression; b = logic_binop; e2 = logic_expression { WISL_Syntax.LBinOp (e1, b, e2) }
  | u = unop; e = logic_expression{ WISL_Syntax.LUnOp (u, e) }
  | LBRACK; l = separated_list(COMMA, logic_expression); RBRACK
    { WISL_Syntax.LEList l }
  

(* We also have lists in the logic *)
logic_binop:
  | b = binop { b }
  | LSTCONS { WISL_Syntax.LSTCONS }
  | LSTCAT { WISL_Syntax.LSTCAT }

logic_value:
  | v = value { v }
  | LSTNIL { WISL_Syntax.VList [] }
