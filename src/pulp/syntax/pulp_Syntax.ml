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

type reference = {
    ref_base : variable;
    ref_field : variable;
    ref_type : reference_type
  }
  
let mk_ref r f rt = {
    ref_base = r;
    ref_field = f;
    ref_type = rt
  }

type codename_spec = spec CodenameMap.t

type builtin_function = (* todo *)
  | Pi of variable * variable

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
    call_scope : variable;
    call_args : variable list;
    call_this : variable;
   }
  
let mk_call name scope vthis args = {
	  call_name = name;
    call_scope = scope;
	  call_args = args;
	  call_this = vthis
  }

type expression = 
  | Literal of literal
  | Var of variable
  | BinOp of variable * bin_op * variable
  | Ref of reference
  | Field of variable
  | Base of variable
  | HasField of variable
  | Lookup of variable 
  | Call of call
  | Obj
  | BuiltInFunction of builtin_function

type assignment = { 
    assign_left : variable; 
    assign_right : expression
  }
  
type mutation = {
    m_left : variable;
    m_right : variable;
  }
  
let mk_mutation r v = {
    m_left = r;
    m_right = v;
  }

type statement =
  | Skip
  | Label of label
  | Assignment of assignment
  | Mutation of mutation
  | Deallocation of variable
  | Goto of string list
  | Assume of Logic.formula
  | Assert of Logic.formula
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