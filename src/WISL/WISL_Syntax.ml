type unop =
  | NOT

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

type variable = string

type expr =
  | Val of value
  | Var of variable
  | BinOp of expr * binop * expr
  | UnOp of unop * expr


type record = (prop_name * expr) list

type statement = 
  | Skip
  | VarAssign of variable * expr
  | Seq of statement * statement
  | New of variable * record
  | Delete of expr
  | PropLookup of variable * expr * prop_name
  | PropUpdate of expr * prop_name * expr
  | FunCall of variable * function_name * (expr list)
  | While of expr * statement
  | If of expr * statement * statement

type var_name_list = variable list

type wisl_fun = function_name * (variable list) * statement * expr

type function_context = wisl_fun list

type program = { context: function_context; entry_point: statement option}


let expr_of_int i = Val (Num (Int i))
let expr_of_float f = Val(Num (Float f))
let expr_of_str s = Val (Str s)