type spec = { (* Move to spec *)
     spec_pre : Logic.formula;
     spec_post : Logic.formula
  }
  
type builtin_loc = 
  | Lg (* Global Object *)
  | Lop (* Object.Prototype Object *)
  | Lfp (* Function.Prototype Object *)
  | LEval (* Eval Function Object *)
  | LRError (* Reference Error *)
  | LTError (* Type Error *)
  | LSError (* Syntax Error *)
  | LNotImplemented (* The tool cannot handle this case atm *)

type builtin_field =
  | FProto
  | FId
  | FScope
  | FPrototype


type reference_type = 
  | MemberReference (*A reference created by access x[y] *)
  | VariableReference (* A reference created by sigma *)

type pulp_type =
  | NullType
  | UndefinedType
  | BooleanType
  | StringType
  | NumberType
  | ObjectType
  | ReferenceType of reference_type option (* Option means member or variable *)

type literal =
  | LLoc of builtin_loc
  | Null                  
  | Bool of bool          
  | Num of float          
  | String of string
  | Undefined
  | Type of pulp_type
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
  (* TODO | Concat *)

type unary_op = 
  | Not

type expression = 
  | Literal of literal
  | Var of variable
  | BinOp of expression * bin_op * expression
  | UnaryOp of unary_op * expression
  | Ref of expression * expression * reference_type
  | Base of expression
  | Field of expression
  | IsTypeOf of expression * pulp_type
  | TypeOf of expression

type call = { 
    call_name : expression;
    call_scope : expression;
    call_args : expression list;
    call_this : expression;
    call_throw_label : label;
   }
  
let mk_call name scope vthis args throwl = {
      call_name = name;
      call_scope = scope;
      call_args = args;
      call_this = vthis;
      call_throw_label = throwl
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
  
type assign_right_expression =
  | Expression of expression
  | Call of call
  | Eval of call
  | Obj
  | HasField of expression * expression
  | Lookup of expression * expression
  | Deallocation of expression * expression
  | ProtoF of expression * expression
  | ProtoO of expression * expression

type assignment = { 
    assign_left : variable; 
    assign_right : assign_right_expression
  }
  
type basic_statement =
  | Skip
  | Assignment of assignment
  | Mutation of mutation

type statement =
  | Label of label
  | Goto of string
  | GuardedGoto of expression * string * string
  | Basic of basic_statement 
  | Sugar of syntactic_sugar_statement
and
syntactic_sugar_statement =
  | If of expression * statement list * statement list 

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
  
  type translation_ctx = { (* Special constants for throws and returns *)
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