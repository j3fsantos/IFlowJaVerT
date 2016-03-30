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
  | LArray (* Array *)
  | Lap (* Array.prototype *)
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
  | Array_Call
  | Array_Construct
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
  | FConstructId
  | FPrimitiveValue
  | FTargetFunction
  | FClass (* TODO : Update Everywhere *)

let string_of_builtin_field f =
  match f with
    | FProto -> "#proto"
    | FId -> "#fid"
    | FScope -> "#scope"
    | FConstructId -> "#constructid"
    | FPrimitiveValue -> "#primvalue"
    | FTargetFunction -> "#targetfunction"
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
  | BField of builtin_field
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
  
let mk_assign_e var e = mk_assign var (Expression e)
let mk_assign_lit var lit = mk_assign_e var (Literal lit)

(* Assignment to a fresh variable *)
let mk_assign_fresh exp = mk_assign (fresh_r ()) exp
  
let mk_assign_fresh_e e = mk_assign_fresh (Expression e)
let mk_assign_fresh_lit lit = mk_assign_fresh_e (Literal lit)
  
type basic_statement =
  | Skip
  | Assignment of assignment
  | Mutation of mutation

(* TODO InnerCall *)
(* TODO refactor the code to use specification functions *)
type specification_function =
    (* 8.7.1 GetValue *)
  | GetValue of expression
    (* 8.7.2 PutValue *)
  | PutValue of expression * expression

    (* [[GetOwnProperty]] *)
  | GetOwnProperty of expression * expression
    (* 8.12.1 [[GetOwnProperty]] *)
  | GetOwnPropertyDefault of expression * expression
    (* 15.5.5.2 [[GetOwnProperty]] *)
  | GetOwnPropertyString of expression * expression
  
    (* [[Get]]*)
  | Get of expression * expression
    (* 8.12.3 [[Get]] *)
  | GetDefault of expression * expression
    (* 15.3.5.4 [[Get]]*)
  | GetFunction of expression * expression

    (* 8.12.5 [[Put]] *)
  | Put of expression * expression * expression * bool
  
    (* 8.12.6 [[HasProperty]] *)
  | HasProperty of expression * expression

    (* 8.12.7 [[Delete]] *)
  | Delete of expression * expression * bool
  
    (* 8.12.8 [[DefaultValue]] *)
  | DefaultValue of expression * pulp_type option

    (* [[DefineOwnProperty]]*)
  | DefineOwnProperty of expression * expression * expression * bool
    (* 8.12.9 [[DefineOwnProperty]]*)
  | DefineOwnPropertyDefault of expression * expression * expression * bool
    (* 15.4.5.1 [[DefineOwnProperty]]*)
  | DefineOwnPropertyArray of expression * expression * expression * bool

    (* 9.1 ToPrimitive *)
  | ToPrimitive of expression * pulp_type option
    (* 9.2 ToBoolean *)
  | ToBoolean of expression
    (* 9.3 ToNumber *)
  | ToNumber of expression
  | ToNumberPrim of expression
    (* 9.6 ToUint32 *)
  | ToUint32 of expression
    (* 9.8 ToString *)
  | ToString of expression 
  | ToStringPrim of expression
    (* 9.9 ToObject *)
  | ToObject of expression
    (* 9.10 CheckObjectCoercible *)
  | CheckObjectCoercible of expression
    (* 9.11 IsCallable *)
  | IsCallable of expression
    (* 11.8.5 The Abstract Relational Comparison Algorithm *)
  | AbstractRelation of expression * expression * bool
    (* 11.9.6 The Strict Equality Comparison Algorithm *)
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
and
syntactic_sugar_statement =
  | If of expression * statement list * statement list 
  (* TODO: Add label option for the specification functions that never throw an exception *)
  | SpecFunction of variable * specification_function * label

let mk_stmt data stx = {stmt_stx = stx; stmt_data = data}

let mk_stmts data stxs = List.map (mk_stmt data) stxs

let empty_metadata = {src_offset = None; stmt_annots = []; loop_head = false}

let mk_stmt_empty_data stx = mk_stmt empty_metadata stx

let mk_stmts_empty_data stxs = List.map mk_stmt_empty_data stxs

let tr_metadata exp = {src_offset = Some exp.Parser_syntax.exp_offset; stmt_annots = exp.Parser_syntax.exp_annot; loop_head = false}

let tr_metadata_loop_head exp = {src_offset = Some exp.Parser_syntax.exp_offset; stmt_annots = exp.Parser_syntax.exp_annot; loop_head = true}
