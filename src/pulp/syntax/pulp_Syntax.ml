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
  | Member of reference
  | Lookup of reference 
  | Call of call
  | Fun of codename 
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
  | Deallocation of reference
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


let make_function_block fn fb fparams fret fexcep = {
    func_name = fn;
    func_body = fb;
    func_params = fparams;
    func_ret = fret;
    func_excep = fexcep;
  }
