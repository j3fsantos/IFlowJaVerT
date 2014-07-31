type spec = { (* Move to spec *)
     spec_pre : Logic.formula;
     spec_post : Logic.formula
  }

type literal =
  | Null                  
  | Bool of bool          
  | Num of float          
  | String of string
  | Undefined
  | Empty (* special return value for the statements and internal reductions *)     

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

type reference_type = 
  | MemberReference (*A reference created by access x[y] *)
  | VariableReference (* A reference created by sigma *)

type codename_spec = spec CodenameMap.t  

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

type expression = 
  | Literal of literal
  | Var of variable
  | BinOp of expression * bin_op * expression
  | Ref of expression * expression * reference_type
  | Base of expression
  | Field of expression
  (* Assignment expressions *)
  | Call of call
  | Obj
  | HasField of expression * expression
  | Lookup of expression * expression
  | Deallocation of expression * expression
  | Pi of expression * expression
and call = { 
    call_name : expression;
    call_scope : expression;
    call_args : expression list;
    call_this : expression;
   }
  
let mk_call name scope vthis args = {
      call_name = name;
      call_scope = scope;
      call_args = args;
      call_this = vthis
  }

type assignment = { 
    assign_left : variable; 
    assign_right : expression
  }
  
type mutation = {
    m_loc : expression;
    m_field : expression;
    m_right : expression;
  }
  
let mk_mutation l f v = {
    m_loc = l;
    m_field = f;
    m_right = v;
  }

type statement =
  | Skip
  | Label of label
  | Goto of string list
  | Assume of Logic.formula
  | Assert of Logic.formula
  | Assignment of assignment
  | Mutation of mutation
  | Sugar of syntactic_sugar_statement
and
syntactic_sugar_statement =
  | If of Logic.formula * statement list * statement list 

type function_id = string

let fresh_variable =
  let counter = ref 0 in
  let rec f name =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f
  
let fresh_r () : variable =
  fresh_variable "r"

type ctx_variables = {
     func_id : function_id;
     fun_bindings : variable list
  }
  
let make_ctx_vars fid vars = 
  { 
    func_id = fid;
    fun_bindings = vars
  }
  
  type translation_ctx = {
    env_vars : ctx_variables list; 
    return_var : variable;
    throw_var : variable;
    label_return : label;
    label_throw : label;
  }
  
let create_ctx env =
  {
     env_vars = env;
     return_var = fresh_r ();
     throw_var = fresh_r ();
     label_return = "return." ^ fresh_r ();
     label_throw = "throw." ^ fresh_r ();
  }
  
type function_block = { 
    func_name : codename;
    func_body : statement list;
    func_params : formal_param list;
    func_ctx : translation_ctx;
}


let make_function_block fn fb fparams ctx = {
    func_name = fn;
    func_body = fb;
    func_params = fparams;
    func_ctx = ctx
  }
  
module AllFunctions = Map.Make ( 
  struct 
    type t = function_id
    let compare = compare
  end
)