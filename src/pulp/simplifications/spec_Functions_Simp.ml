(* ./src/pulp/simplifications/spec_Functions_Simp.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open Pulp_Syntax
open Pulp_Translate_Aux
open Simp_Common
open Type_Info

(* TODO : Check if throwing exceptions is correct.*)

let simplify_get_value e left annot throw_var label_throw =
  let simplify_not_a_ref = Some [Basic (Assignment (mk_assign left (Expression e)))] in
  
  let simplify_ref_object e1 e1_ty e2 rt =
    match rt with
       | MemberReference ->  Some (translate_gamma_member_reference_object e1 e2 left)
       | VariableReference ->
        begin match e1 with
           | Literal (LLoc Lg) -> Some (translate_gamma_variable_reference_object_lg e1 e2 left)
           | Literal (LLoc _) ->  Some (translate_gamma_variable_reference_object_not_lg e1 e2 left)
           | Literal _ | BinOp _ | UnaryOp _ | Base _ | Field _ | TypeOf _ | Ref _ ->  raise (Invalid_argument "Cannot Happen in simplify_ref_object") 
           | Var v ->
            begin match e1_ty with
              | Some Normal -> (* Definetely not Lg *) Some (translate_gamma_variable_reference_object_not_lg e1 e2 left)
              | Some Builtin -> Some (translate_gamma_variable_reference_object e1 e2 left)
              | None -> raise (Invalid_argument "Cannot Happen in simplify_ref_object for object type in get value")
            end 
        end
    in
    
  match e with
    | Literal _ | BinOp _ | UnaryOp _ | Base _ | Field _ | TypeOf _ -> simplify_not_a_ref
    | Var var -> 
      begin match get_type_info annot var with
        | None -> None
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType | UndefinedType | BooleanType | StringType | NumberType | ObjectType _ -> simplify_not_a_ref
                | ReferenceType _ -> None  
              end
            | TI_Value | TI_NotARef -> simplify_not_a_ref
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to get_value")
          end
      end
    | Ref (e1, e2, rt) -> 
      begin match e1 with
        | Literal lit ->
          begin match lit with
            | LLoc l -> simplify_ref_object e1 None e2 rt
            | Null ->  None            
            | Bool _  | Num _  | String _ ->  None
            | Undefined -> Some (translate_error_throw Lrep throw_var label_throw)
            | Type pt -> raise (Invalid_argument "Type cannot be as an argument to Reference")
            | Empty -> raise (Invalid_argument "Empty cannot be as an argument to Reference")   
           end
        | BinOp _ 
        | UnaryOp _ -> None
        | Field _ -> None
        | TypeOf _ -> raise (Invalid_argument "Not well formed expression Ref (BinOp | UnartOp | Field | TypeOf, _, _)") (* To introduce well formed expressions in normal form? *)
        | Base _ -> None
        | Var var ->        
            begin match get_type_info annot var with
              | None -> None
              | Some pt ->
                begin match pt with
                  | TI_Type pt ->
                    begin match pt with
                      | NullType -> None
                      | UndefinedType -> Some (translate_error_throw Lrep throw_var label_throw)
                      | BooleanType | StringType | NumberType -> None
                      | ObjectType ot -> simplify_ref_object e1 ot e2 rt
                      | ReferenceType _ -> raise (Invalid_argument "Reference cannot be as an argument to Reference") 
                    end
                  | TI_Value | TI_NotARef -> None
                  | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to Reference")
                end
          end
        | Ref _ -> raise (Invalid_argument "Reference cannot be as an argument to Reference")
     end