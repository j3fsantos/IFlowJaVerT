(* ./src/pulp/simplifications/type_Info.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open Pulp_Syntax

type type_info = 
  | TI_Type of pulp_type
  | TI_Value (* Not a Reference && Not Empty *)
  | TI_NotARef
  | TI_Empty

let ground_type pt =
  match pt with
    | NullType | UndefinedType | StringType | NumberType | BooleanType | ObjectType (Some Builtin) 
    | ObjectType (Some Normal) | ReferenceType (Some MemberReference) | ReferenceType (Some VariableReference) -> true
    | ObjectType None | ReferenceType None -> false

let type_lt t1 t2 =
  match (t1, t2) with
    | ReferenceType (Some MemberReference), ReferenceType None 
    | ReferenceType (Some VariableReference), ReferenceType None 
    | ObjectType (Some Normal), ObjectType None
    | ObjectType (Some Builtin), ObjectType None -> true
    | _, _ -> false

let get_pulp_type typeinfo =
  match typeinfo with
    | TI_Type pt -> Some pt
    | TI_Value | TI_NotARef | TI_Empty -> None

let string_of_type_info ty = 
  match ty with
    | TI_Type pt -> Pulp_Syntax_Print.string_of_pulp_type pt
    | TI_Value -> "TI_Value"
    | TI_NotARef -> "TI_NotARef"
    | TI_Empty -> "TI_Empty"

let upper_bound_type t1 t2 =
  if t1 = t2 then t1 else 
    begin match t1, t2 with
      | None, _ -> None
      | _, None -> None
      | Some t1, Some t2 -> 
        begin match t1, t2 with
          | TI_Type (ReferenceType _), TI_Type (ReferenceType _) -> Some (TI_Type (ReferenceType None))
          | TI_Type (ReferenceType _), _ -> None
          | _, TI_Type (ReferenceType _) -> None
          | TI_Type (ObjectType _), TI_Type (ObjectType _) -> Some (TI_Type (ObjectType None))
          | TI_Empty, _ -> Some TI_NotARef
          | _, TI_Empty -> Some TI_NotARef
          | _, TI_NotARef -> Some TI_NotARef
          | TI_NotARef, _ -> Some TI_NotARef
          | _, _ -> Some (TI_Value)
        end
    end
    
let empty_type_info x = None


let get_type_info_literal lit =
  match lit with
    | LLoc _ -> TI_Type (ObjectType (Some Builtin))
    | Null -> TI_Type NullType               
    | Bool _ -> TI_Type BooleanType         
    | Num _ -> TI_Type NumberType          
    | String _ -> TI_Type StringType
    | Undefined -> TI_Type UndefinedType
    | Type _ ->  TI_Type StringType (* TODO *)
    | Empty -> TI_Empty

let get_type_info_expr type_info e =
  match e with
    | Literal l -> Some (get_type_info_literal l)
    | Var v -> type_info v
    | BinOp (e1, binop, e2) -> 
      begin match binop with
        | Concat -> Some (TI_Type StringType)
        | Comparison _ -> Some (TI_Type BooleanType) 
        | Arith aop ->  Some (TI_Type NumberType)
        | Boolean bop -> Some (TI_Type BooleanType) 
        | Bitwise _ -> Some (TI_Type NumberType) 
      end
    | UnaryOp (Not, e) -> Some (TI_Type BooleanType)
    | UnaryOp (Negative, e) -> Some (TI_Type NumberType)
    | UnaryOp (ToStringOp, e) -> Some (TI_Type StringType)
    | UnaryOp (ToNumberOp, e) -> Some (TI_Type NumberType)
    | UnaryOp (ToInt32Op, e) -> Some (TI_Type NumberType)
    | UnaryOp (ToUint32Op, e) -> Some (TI_Type NumberType)
    | UnaryOp (BitwiseNot, e) -> Some (TI_Type NumberType)
    | Ref (e1, e2, ref_type) -> Some (TI_Type (ReferenceType (Some ref_type)))
    | Base e -> Some TI_Value
    | Field e -> Some (TI_Type StringType)
    | TypeOf e -> Some (TI_Type StringType)

let get_type_info_assign_expr type_info e =
  let f = get_type_info_expr type_info in
  match e with
      | Expression expr -> f expr
      | Call c 
      | Eval c 
      | BuiltinCall c -> Some TI_Value (* To check for builtin function calls *)
      | Obj -> Some (TI_Type (ObjectType (Some Normal)))
      | HasField (e1, e2) -> Some (TI_Type BooleanType)
      | Lookup (e1, e2) -> Some TI_Value
      | Deallocation (e1, e2) -> Some (TI_Type BooleanType)
      | ProtoF (e1, e2) -> Some TI_NotARef
      | ProtoO (e1, e2) -> Some (TI_Type (BooleanType))