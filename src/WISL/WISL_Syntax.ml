(* WISL Syntax *)

type unop =
  | NOT
  (* Lists are only for the logic *)
  | LEN
  | HEAD
  | TAIL

type binop =
  | NEQ
	| EQUAL
	| LESSTHAN
	| GREATERTHAN
	| LESSEQUAL
	| GREATEREQUAL
	| PLUS
	| MINUS
	| TIMES
	| DIV
	| MOD
	| AND
	| OR
  (* Lists are only for the logic *)
  | LSTCONS (* list construction a::l, only for logic *)
  | LSTCAT  (* list concatenation, only for logic *)

type prop_name = string
type function_name = string
type number =
  | Int of int
  | Float of float

type value =
  | Bool of bool
  | Loc of string
  | Num of number
  | Str of string
  | Null
  | VList of value list

type variable = string

type expr =
  | Val of value
  | Var of variable
  | BinOp of expr * binop * expr
  | UnOp of unop * expr


type record = (prop_name * expr) list


(* WISL Logic (subset of JSIL Logic) *)

type logic_variable = string

type logic_expr =
  | LVal of value 
  | LVar of logic_variable
  | PVar of variable
  | LBinOp of logic_expr * binop * logic_expr
  | LUnOp of unop * logic_expr
  | LEList of logic_expr list


type logic_assertion =
  | LTrue
  | LFalse
  | LNot of logic_assertion
  | LAnd of logic_assertion * logic_assertion
  | LOr of logic_assertion * logic_assertion
  | LEmp
  | LStar of logic_assertion * logic_assertion
  | LPred of string * logic_expr list
  | LPointsTo of logic_expr * prop_name * logic_expr
  | LEq of logic_expr * logic_expr
  | LLess of logic_expr * logic_expr
  | LGreater of logic_expr * logic_expr
  | LLessEq of logic_expr * logic_expr
  | LGreaterEq of logic_expr * logic_expr


type specification = {
  pre: logic_assertion;
  post: logic_assertion; (* At first, only one post-condition *)
}


type logic_predicate = {
  pred_name: string;
  pred_params: variable list;
  pred_definitions: ((string option) * logic_assertion) list;
}

type logic_command =
  | Fold of logic_assertion
  | Unfold of logic_assertion 
  | ApplyLem of string * (logic_expr list)
  | RecUnfold of string
  | LogicIf of logic_expr * (logic_command list) * (logic_command list)
  | Assert of logic_assertion

type wisl_metadata = {
  precmds: logic_command list;
  postcmds: logic_command list;
  invariant: logic_assertion option;
}

type wisl_lemma =  {
  lemma_name: string;
  lemma_params: variable list;
  proof: (logic_command list) option;
  variant: expr option;
  hypothesis: logic_assertion;
  conclusions: logic_assertion list;
}

(* Programs and functions *)

type statement = 
  | Skip
  | VarAssign of variable * expr
  | New of variable * record
  | Delete of expr
  | PropLookup of variable * expr * prop_name
  | PropUpdate of expr * prop_name * expr
  | FunCall of variable * function_name * (expr list)
  | While of expr * (statement_with_metadata list)
  | If of expr * (statement_with_metadata list) * (statement_with_metadata list)
and statement_with_metadata = (wisl_metadata * statement)

type wisl_fun = {
  name: function_name;
  params: variable list;
  body: statement_with_metadata list;
  spec: specification option;
  return_expr: expr;
}

type function_context = wisl_fun list

type program = {
  context: function_context;
  predicates: logic_predicate list;
  lemmas: wisl_lemma list;
  entry_point: (statement_with_metadata list) option
}