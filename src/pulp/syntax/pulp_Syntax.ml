(* ./src/pulp/syntax/pulp_Syntax.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

type feature =
  | GetValuePrim
  | ToNumber
  | ToString
  | ToObject
  
type builtin_loc = 
  | Lg (* Global Object *)
  | Lg_isNaN
  | Lg_isFinite
  | Lop (* Object.Prototype Object *)
  | Lop_toString
  | Lop_valueOf
  | Lop_isPrototypeOf
  | LFunction
  | Lfp (* Function.Prototype Object *)
  | LEval (* Eval Function Object *)
  | LError 
  | Lep
  | LRError (* Reference Error *)
  | Lrep
  | LTError (* Type Error *)
  | Ltep
  | LSError (* Syntax Error *)
  | Lsep
  | LEvalError
  | LEvalErrorP
  | LRangeError
  | LRangeErrorP
  | LURIError
  | LURIErrorP
  | LObject (* Object Object *)
  | LObjectGetPrototypeOf
  | LBoolean (* Boolean Object *)
  | Lbp (* Boolean.prototype *)
  | Lbp_toString
  | Lbp_valueOf
  | LNumber 
  | Lnp 
  | Lnp_toString 
  | Lnp_valueOf 
  | LMath
  | LString 
  | Lsp 
  | Lsp_toString 
  | Lsp_valueOf
  | LJSON
  | LNotImplemented of feature (* The tool cannot handle this case atm *)
  | LStub of string

type builtin_function = 
  | Global_eval
  | Global_isNaN
  | Global_isFinite
  | Boolean_Call
  | Boolean_Construct
  | Boolean_Prototype_toString
  | Boolean_Prototype_valueOf
  | Object_Call
  | Object_Construct
  | Object_getPrototypeOf
  | Object_Prototype_toString
  | Object_Prototype_valueOf
  | Object_Prototype_isPrototypeOf
  | Number_Call 
  | Number_Construct 
  | Number_Prototype_toString 
  | Number_Prototype_valueOf 
  | String_Call 
  | String_Construct 
  | String_Prototype_toString 
  | String_Prototype_valueOf 
  | Error_Call_Construct
  | TypeError_Call_Construct
  | ReferenceError_Call_Construct
  | SyntaxError_Call_Construct
  | EvalError_Call_Construct
  | RangeError_Call_Construct
  | URIError_Call_Construct
  | Function_Call
  | Function_Construct
  | Function_Prototype_Call
  | Not_Implemented_Stub of string

type builtin_field =
  | FProto
  | FId
  | FScope
  | FPrototype
  | FConstructId
  | FPrimitiveValue
  | FClass (* TODO : Update Everywhere *)

let string_of_builtin_field f =
  match f with
    | FProto -> "#proto"
    | FId -> "#fid"
    | FScope -> "#scope"
    | FPrototype -> "prototype"
    | FConstructId -> "#constructid"
    | FPrimitiveValue -> "#primvalue"
    | FClass -> "#class"

type reference_type = 
  | MemberReference (*A reference created by access x[y] *)
  | VariableReference (* A reference created by sigma *)

type object_type =
  | Normal
  | Builtin

type pulp_type =
  | NullType
  | UndefinedType
  | BooleanType
  | StringType
  | NumberType
  | ObjectType of object_type option
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

type comparison_op =
  | Equal
  | LessThan (* TODO : Have a different one for strings? *)
  | LessThanEqual

type arith_op =
  | Plus
  | Minus
  | Times
  | Div
  | Mod

type bool_op =
  | And 
  | Or

type bitwise_op =
  | BitwiseAnd
  | BitwiseOr
  | BitwiseXor
  | LeftShift
  | SignedRightShift
  | UnsignedRightShift

type bin_op = 
  | Comparison of comparison_op
  | Arith of arith_op
  | Subtype
  | Concat
  | Boolean of bool_op
  | Bitwise of bitwise_op

type unary_op = 
  | Not
  | Negative
  | ToStringOp
  | ToNumberOp
  | ToInt32Op
  | ToUint32Op
  | BitwiseNot

type expression = 
  | Literal of literal
  | Var of variable
  | BinOp of expression * bin_op * expression
  | UnaryOp of unary_op * expression
  | Ref of expression * expression * reference_type
  | Base of expression
  | Field of expression
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

(* scalls - calls with numeric labels*) 
type scall = { 
    scall_name : expression;
    scall_scope : expression;
    scall_args : expression list;
    scall_this : expression;
    scall_throw_label : int;
}
  
let mk_scall name scope vthis args int_label = {
      scall_name = name;
      scall_scope = scope;
      scall_args = args;
      scall_this = vthis;
      scall_throw_label = int_label
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
  | BuiltinCall of call (* Have eval here? *)
  | Obj
  | HasField of expression * expression
  | Lookup of expression * expression
  | Deallocation of expression * expression
  | ProtoF of expression * expression (* TODO: A bit different for String Objects. *)
  | ProtoO of expression * expression

type assignment = { 
    assign_left : variable; 
    assign_right : assign_right_expression
  }
  
let fresh_variable =
  let counter = ref 0 in
  let rec f name =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f
  
let fresh_r () : variable =
  fresh_variable "r"
  
(* Assignment *)
let mk_assign var exp = { 
    assign_left = var; 
    assign_right = exp
  }

(* Assignment to a fresh variable *)
let mk_assign_fresh exp = mk_assign (fresh_r ()) exp
  
let mk_assign_fresh_e e = mk_assign_fresh (Expression e)
let mk_assign_fresh_lit lit = mk_assign_fresh_e (Literal lit)
  
type basic_statement =
  | Skip
  | Assignment of assignment
  | Mutation of mutation

type specification_function =
  | GetValue of expression
  | PutValue of expression * expression
  | Get of expression * expression
  | HasProperty of expression * expression
  | DefaultValue of expression * pulp_type option
  (* TODO | InnerCall *)
  | ToPrimitive of expression * pulp_type option
  | ToBoolean of expression
  | ToNumber of expression
  | ToNumberPrim of expression
  | ToString of expression 
  | ToStringPrim of expression
  | ToObject of expression
  | CheckObjectCoercible of expression
  | IsCallable of expression
  | AbstractRelation of expression * expression * bool
  | StrictEquality of expression * expression
  | StrictEqualitySameType of expression * expression

type statement_metadata = {
  src_offset : int option; 
  stmt_annots : Parser_syntax.annotation list;
  loop_head : bool
}

type statement = {
  stmt_stx : statement_syntax; 
  stmt_data : statement_metadata;
}
and statement_syntax =
  | Label of label
  | Goto of string
  | GuardedGoto of expression * string * string
  | Basic of basic_statement 
  | Sugar of syntactic_sugar_statement
(* numbered gotos - no more labels *)
and
syntactic_sugar_statement =
  | If of expression * statement list * statement list 
  | SpecFunction of variable * specification_function * label

let mk_stmt data stx = {stmt_stx = stx; stmt_data = data}

let mk_stmts data stxs = List.map (mk_stmt data) stxs

let empty_metadata = {src_offset = None; stmt_annots = []; loop_head = false}

let mk_stmt_empty_data stx = mk_stmt empty_metadata stx

let mk_stmts_empty_data stxs = List.map mk_stmt_empty_data stxs

let tr_metadata exp = {src_offset = Some exp.Parser_syntax.exp_offset; stmt_annots = exp.Parser_syntax.exp_annot; loop_head = false}

let tr_metadata_loop_head exp = {src_offset = Some exp.Parser_syntax.exp_offset; stmt_annots = exp.Parser_syntax.exp_annot; loop_head = true}
