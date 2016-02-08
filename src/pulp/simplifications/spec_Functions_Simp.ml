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
    
let simplify_put_value e1 e2 annot throw_var label_throw =
  let gotothrow = Some (translate_error_throw Lrep throw_var label_throw) in
    
  match e1 with
    | Literal _ | BinOp _ | UnaryOp _ | Base _ | Field _ | TypeOf _ -> gotothrow
    | Var var -> 
      begin match get_type_info annot var with
        | None -> None
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType | UndefinedType | BooleanType | StringType | NumberType | ObjectType _ -> gotothrow
                | ReferenceType _ ->  None
              end
            | TI_Value | TI_NotARef -> gotothrow
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to get_value")
          end
      end
    | Ref (base, field, rt) -> 
      begin match base with
        | Literal lit ->
          begin match lit with
            | LLoc l -> Some (translate_put_value_reference_object_base_field base field e2)
            | Null ->  None             
            | Bool _  | Num _  | String _ -> gotothrow
            | Undefined -> gotothrow
            | Type pt -> raise (Invalid_argument "Type cannot be as an argument to Reference")
            | Empty -> raise (Invalid_argument "Empty cannot be as an argument to Reference")   
           end
        | BinOp _ 
        | UnaryOp _ -> None
        | Field _ -> gotothrow (* Field (_) always return string *)
        | TypeOf _ -> raise (Invalid_argument "Not well formed expression Ref (BinOp | UnartOp | Field | TypeOf, _, _)") (* To introduce well formed expressions in normal form? *)
        | Base _ -> (* TODO *) None (* if it's base of some variable and we know that variable is a type of member of object reference  *)
        | Var var ->        
            begin match get_type_info annot var with
              | None -> None
              | Some pt ->
                begin match pt with
                  | TI_Type pt ->
                    begin match pt with
                      | NullType -> None
                      | UndefinedType -> gotothrow
                      | BooleanType | StringType | NumberType -> gotothrow
                      | ObjectType ot -> Some (translate_put_value_reference_object_base_field base field e2)
                      | ReferenceType _ -> raise (Invalid_argument "Reference cannot be as an argument to Reference") 
                    end
                  | TI_Value | TI_NotARef -> None
                  | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to Reference")
                end
          end
        | Ref _ -> raise (Invalid_argument "Reference cannot be as an argument to Reference")
     end
      
let simplify_to_number_prim e annot left =
  match e with
    | Literal Undefined -> Some [assign_num left nan]
    | Literal Null | Literal (Bool false) -> Some [assign_num left 0.0]
    | Literal (Bool true) -> Some [assign_num left 1.0]
    | Literal (String s) -> Some [assign_to_number left s] 
    | Literal (Num n) -> Some [assign_num left n]
    | Literal Empty | Literal (LLoc _) | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "To number prim cannot take empty / object / type / typeof / ref as an argument") 
    | Field _ -> Some [assign_uop left ToNumberOp e] (* Field return string *)
    | BinOp _ | UnaryOp _ | Base _ -> None  (* TODO: Different types for different operators *)
    | Var var -> 
      begin match get_type_info annot var with
        | None -> None
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType -> Some [assign_num left 0.0]
                | UndefinedType -> Some [assign_num left nan]
                | BooleanType -> Some (translate_to_number_bool e left)
                | StringType -> Some [assign_uop left ToNumberOp e]
                | NumberType -> Some [assign_expr left e]
                | ObjectType _
                | ReferenceType _ -> raise (Invalid_argument "To number prim cannot take objects and references as arguments") 
              end
            | TI_Value | TI_NotARef -> None
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to to_number_prim")
          end
      end
      
let simplify_to_number e annot left throw_var label_throw =
  match e with
    | Literal (LLoc _) -> None
    | Literal Undefined | Literal Null | Literal (Bool _) | Literal (String _) | Literal (Num _) | Field _ | BinOp _ | UnaryOp _ -> simplify_to_number_prim e annot left
    | Literal Empty | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "To number cannot take empty / type / ref as an argument") 
    | Base _ -> None
    | Var var -> 
      begin match get_type_info annot var with
        | None -> None
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType | UndefinedType | BooleanType | StringType | NumberType -> simplify_to_number_prim e annot left
                | ObjectType _ -> None
                | ReferenceType _ -> raise (Invalid_argument "To number cannot take and references as arguments") 
              end
            | TI_Value | TI_NotARef -> None
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to to_number")
          end
      end
      
let simplify_to_string_prim e annot left =
  match e with
    | Literal Undefined -> Some [assign_string left "undefined"]
    | Literal Null -> Some [assign_string left "null"]
    | Literal (Bool false) -> Some [assign_string left "false"]
    | Literal (Bool true) -> Some [assign_string left "true"]
    | Literal (String s) -> Some [assign_string left s] 
    | Literal (Num n) -> Some [assign_to_string left n]
    | Literal Empty | Literal (LLoc _) | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "To_string_prim cannot take empty / object / type / ref / base as an argument") 
    | Field _ -> Some [assign_expr left e] (* Field return string *)
    | BinOp _ | UnaryOp _  | Base _ -> None (* TODO: Different types for different operators *)
    | Var var -> 
      begin match get_type_info annot var with
        | None -> None
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType -> Some [assign_string left "null"]
                | UndefinedType -> Some [assign_string left "undefined"]
                | BooleanType -> Some (translate_to_string_bool e left)
                | StringType -> Some [assign_expr left e]
                | NumberType -> Some [assign_uop left ToStringOp e]
                | ObjectType _
                | ReferenceType _ -> raise (Invalid_argument "To string prim cannot take objects and references as arguments") 
              end
            | TI_Value | TI_NotARef -> None
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to to_string_prim")
          end
      end
      
let simplify_to_string e annot left throw_var label_throw =
  match e with
    | Literal (LLoc _) -> None
    | Literal Undefined | Literal Null | Literal (Bool _) | Literal (String _) | Literal (Num _) | Field _ | BinOp _ | UnaryOp _ -> simplify_to_string_prim e annot left
    | Literal Empty | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "To string cannot take empty / type / typeof / ref as an argument") 
    | Base _ -> None
     | Var var -> 
      begin match get_type_info annot var with
        | None -> None
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType | UndefinedType | BooleanType | StringType | NumberType -> simplify_to_string_prim e annot left
                | ObjectType _ -> None
                | ReferenceType _ -> raise (Invalid_argument "To_string cannot take and references as arguments") 
              end
            | TI_Value | TI_NotARef -> None
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to to_string")
          end
      end
      
let simplify_to_object e annot left throw_var label_throw =
  match e with
    | Literal (LLoc _) -> Some [assign_expr left e]
    | Literal Undefined | Literal Null -> Some (translate_error_throw Ltep throw_var label_throw)
    | Literal (Bool _) -> Some (make_builtin_call (Boolean_Construct) left None [e] throw_var label_throw)
    | Literal (String _) | Field _ -> Some (make_builtin_call (String_Construct) left None [e] throw_var label_throw)
    | Literal (Num _) -> Some (make_builtin_call (Number_Construct) left None [e] throw_var label_throw)
    | BinOp _ | UnaryOp _ -> None (* TODO simplify more for the specific op *)
    | Literal Empty | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "To object cannot take empty / type / ref as an argument") 
    | Base _ -> None
    | Var var -> 
      begin match get_type_info annot var with
        | None -> None
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType | UndefinedType -> Some (translate_error_throw Ltep throw_var label_throw)
                | BooleanType -> Some (make_builtin_call (Boolean_Construct) left None [e] throw_var label_throw)
                | StringType -> Some (make_builtin_call (String_Construct) left None [e] throw_var label_throw)
                | NumberType -> Some (make_builtin_call (Number_Construct) left None [e] throw_var label_throw)
                | ObjectType _ -> Some [assign_expr left e]
                | ReferenceType _ -> raise (Invalid_argument "To_object cannot take and references as arguments") 
              end
            | TI_Value | TI_NotARef -> None
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to to_object")
          end
      end
      
let simplify_to_primitive e preftype annot left throw_var label_throw =
  match e with
    | Literal (LLoc _) -> None
    | Literal Undefined | Literal Null | Literal (Bool _) | Literal (String _) | Field _ | Literal (Num _) | BinOp _ | UnaryOp _ -> Some [assign_expr left e]
    | Literal Empty | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "To object cannot take empty / type / typeof / ref as an argument") 
    | Base _ -> None
    | Var var -> 
      begin match get_type_info annot var with
        | None -> None
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType | UndefinedType | BooleanType | StringType | NumberType -> Some [assign_expr left e]
                | ObjectType _ -> None
                | ReferenceType _ -> raise (Invalid_argument "To_primitive cannot take and references as arguments") 
              end
            | TI_Value | TI_NotARef -> None
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to to_primitive")
          end
      end
      
let simplify_strict_equality_comparison_types_equal e1 e2 annot left =
  match e1 with
    | Literal Undefined | Literal Null -> Some [assign_true left]
    | Literal (LLoc _) | Literal (Bool _) | Literal (String _) | Field _ -> Some (translate_strict_equality_comparison_types_equal_if_equal e1 e2 left) (* TODO: Do I really want to use field as String? *)
    | Literal (Num n1) ->
      begin
        match e2 with
          | Literal (Num n2) ->
            if (n1 = n2) (* nan != nan and TODO check: 0.0 == -0.0 *) then Some [assign_true left] else Some [assign_false left]
          | _ -> None
      end
    | BinOp _ | UnaryOp _ | Base _ -> None
    | Literal Empty | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "=== same types cannot take empty / type / typeof / ref as an argument") 
    | Var var -> 
      begin match get_type_info annot var with
        | None -> None
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType | UndefinedType -> Some [assign_true left]
                | BooleanType | StringType | ObjectType _ -> Some (translate_strict_equality_comparison_types_equal_if_equal e1 e2 left)
                | NumberType -> None               
                | ReferenceType _ -> raise (Invalid_argument "=== same types cannot take and references as arguments") 
              end
            | TI_Value | TI_NotARef -> None
            | TI_Empty -> raise (Invalid_argument "=== same types cannot be as an argument to IsCallable")
          end
      end
      
let simplify_strict_equality_comparison e1 e2 annot left =

  let type_of_e1 = Type_Info.get_type_info_expr (get_type_info annot) e1 in
  let type_of_e2 = Type_Info.get_type_info_expr (get_type_info annot) e2 in
  
  match type_of_e1, type_of_e2 with
    | None, _
    | _, None -> None
    | Some t1, Some t2 ->
      begin
        let t1 = Type_Info.get_pulp_type t1 in
        let t2 = Type_Info.get_pulp_type t2 in
        begin match t1, t2 with
          | None, _
          | _, None -> None
          | Some t1, Some t2 ->
            if t1 = t2 then simplify_strict_equality_comparison_types_equal e1 e2 annot left
            else Some [assign_false left]
        end
      end