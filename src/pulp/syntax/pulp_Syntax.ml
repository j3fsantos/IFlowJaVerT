type spec = { (* Move to spec *)
     spec_pre : Logic.formula;
     spec_post : Logic.formula
  }

type literal =
  | Null                  
  | Bool of bool          
  | Num of float          
  | String of string      

type variable = string (* Variables of IVL *)

type formal_param = string (* Formal parameters of functions *)

type codename = string

type label = string

module CodenameMap = Map.Make (
  struct 
    type t = codename
    let compare = compare
  end
)

type codename_spec = spec CodenameMap.t

type builtin_function = (* todo *)
  | Sigma of variable
  | Gamma of variable (* Do I want to have types for variables ? For example here we have a reference type for a variable *)
  | ObjCoercible of variable

type comparison_op =
  | Equal

type arith_op =
  | Plus
  | Minus
  | Times
  | Div

type bool_op =
  | And 
  | Or

type bin_op = 
  | Comparison of comparison_op
  | Arith of arith_op
  | Boolean of bool_op

type call = { 
    call_name : variable;
    call_args : variable list;
    call_this : variable;
   }

type expression = 
  | Literal of literal
  | Empty (* special return value for the statements and internal reductions *)
  | Var of variable
  | BinOp of variable * bin_op * variable
  | Member of variable * variable
  | Call of call
  | Fun of codename 
  | Obj
  | BuiltInFunction of builtin_function

type assignment = { 
    assignment_left : variable; 
    assignment_right : expression
  }

type statement =
  | Skip
  | Label of label
  | Assignment of assignment
  | Goto of string list
  | Assume of Logic.formula
  | Assert of Logic.formula
  | Sugar of syntactic_sugar_statement
and
syntactic_sugar_statement =
  | If of Logic.formula * statement list * statement list 

type function_block = { 
    func_name : codename;
    func_body : statement list;
    func_params : formal_param list;
    func_ret : variable;  (* A variable where the function result is stored *)
    func_excep : variable; (* A variable where an exception is stored *)
}
