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

let simplify_get_value e left sf_annot throw_var label_throw =
  let annot = sf_annot.as_annot in 
  let md = sf_annot.as_stmt.stmt_data in
  let mk_stmts_md = mk_stmts md in
  let simplify_not_a_ref = Some (mk_stmts_md [Basic (Assignment (mk_assign left (Expression e)))]) in
  
  let simplify_ref_object e1 e1_ty e2 rt =
    match rt with
       | MemberReference ->  Some (translate_gamma_member_reference_object e1 e2 left md)
       | VariableReference ->
        begin match e1 with
           | Literal (LLoc Lg) -> Some (translate_gamma_variable_reference_object_lg e1 e2 left md)
           | Literal (LLoc _) ->  Some (translate_gamma_variable_reference_object_not_lg e1 e2 left md)
           | Literal _ | BinOp _ | UnaryOp _ | Base _ | Field _ | TypeOf _ | Ref _ ->  raise (Invalid_argument "Cannot Happen in simplify_ref_object") 
           | Var v ->
            begin match e1_ty with
              | Some Normal -> (* Definetely not Lg *) Some (translate_gamma_variable_reference_object_not_lg e1 e2 left md)
              | Some Builtin -> Some (translate_gamma_variable_reference_object e1 e2 left md)
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
            | Undefined -> Some (translate_error_throw Lrep throw_var label_throw md)
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
                      | UndefinedType -> Some (translate_error_throw Lrep throw_var label_throw md)
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
    
let simplify_put_value e1 e2 sf_annot throw_var label_throw =
  let annot = sf_annot.as_annot in 
  let md = sf_annot.as_stmt.stmt_data in
  let gotothrow = Some (translate_error_throw Lrep throw_var label_throw md) in
    
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
            | LLoc l -> Some (translate_put_value_reference_object_base_field base field e2 md)
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
                      | ObjectType ot -> Some (translate_put_value_reference_object_base_field base field e2 md)
                      | ReferenceType _ -> raise (Invalid_argument "Reference cannot be as an argument to Reference") 
                    end
                  | TI_Value | TI_NotARef -> None
                  | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to Reference")
                end
          end
        | Ref _ -> raise (Invalid_argument "Reference cannot be as an argument to Reference")
     end
      
let simplify_to_number_prim e sf_annot left =
  let annot = sf_annot.as_annot in 
  let md = sf_annot.as_stmt.stmt_data in
  let mk_stmts_md = mk_stmts md in
  match e with
    | Literal Undefined -> Some (mk_stmts_md [assign_num left nan])
    | Literal Null | Literal (Bool false) -> Some (mk_stmts_md [assign_num left 0.0])
    | Literal (Bool true) -> Some (mk_stmts_md [assign_num left 1.0])
    | Literal (String s) -> Some (mk_stmts_md [assign_to_number left s]) 
    | Literal (Num n) -> Some (mk_stmts_md [assign_num left n])
    | Literal Empty | Literal (LLoc _) | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "To number prim cannot take empty / object / type / typeof / ref as an argument") 
    | Field _ -> Some (mk_stmts_md [assign_uop left ToNumberOp e]) (* Field return string *)
    | BinOp _ | UnaryOp _ | Base _ -> None  (* TODO: Different types for different operators *)
    | Var var -> 
      begin match get_type_info annot var with
        | None -> None
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType -> Some (mk_stmts_md [assign_num left 0.0])
                | UndefinedType -> Some (mk_stmts_md [assign_num left nan])
                | BooleanType -> Some (translate_to_number_bool e left md)
                | StringType -> Some (mk_stmts_md [assign_uop left ToNumberOp e])
                | NumberType -> Some (mk_stmts_md [assign_expr left e])
                | ObjectType _
                | ReferenceType _ -> raise (Invalid_argument "To number prim cannot take objects and references as arguments") 
              end
            | TI_Value | TI_NotARef -> None
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to to_number_prim")
          end
      end
      
let simplify_to_number e sf_annot left throw_var label_throw =
  let annot = sf_annot.as_annot in 
  match e with
    | Literal (LLoc _) -> None
    | Literal Undefined | Literal Null | Literal (Bool _) | Literal (String _) | Literal (Num _) | Field _ | BinOp _ | UnaryOp _ -> simplify_to_number_prim e sf_annot left
    | Literal Empty | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "To number cannot take empty / type / ref as an argument") 
    | Base _ -> None
    | Var var -> 
      begin match get_type_info annot var with
        | None -> None
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType | UndefinedType | BooleanType | StringType | NumberType -> simplify_to_number_prim e sf_annot left
                | ObjectType _ -> None
                | ReferenceType _ -> raise (Invalid_argument "To number cannot take and references as arguments") 
              end
            | TI_Value | TI_NotARef -> None
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to to_number")
          end
      end
      
let simplify_to_string_prim e sf_annot left =
  let annot = sf_annot.as_annot in 
  let md = sf_annot.as_stmt.stmt_data in
  let mk_stmts_md = mk_stmts md in
  match e with
    | Literal Undefined -> Some (mk_stmts_md [assign_string left "undefined"])
    | Literal Null -> Some (mk_stmts_md [assign_string left "null"])
    | Literal (Bool false) -> Some (mk_stmts_md [assign_string left "false"])
    | Literal (Bool true) -> Some (mk_stmts_md [assign_string left "true"])
    | Literal (String s) -> Some (mk_stmts_md [assign_string left s]) 
    | Literal (Num n) -> Some (mk_stmts_md [assign_to_string left n])
    | Literal Empty | Literal (LLoc _) | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "To_string_prim cannot take empty / object / type / ref / base as an argument") 
    | Field _ -> Some (mk_stmts_md [assign_expr left e]) (* Field return string *)
    | BinOp _ | UnaryOp _  | Base _ -> None (* TODO: Different types for different operators *)
    | Var var -> 
      begin match get_type_info annot var with
        | None -> None
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType -> Some (mk_stmts_md [assign_string left "null"])
                | UndefinedType -> Some (mk_stmts_md [assign_string left "undefined"])
                | BooleanType -> Some (translate_to_string_bool e left md)
                | StringType -> Some (mk_stmts_md [assign_expr left e])
                | NumberType -> Some (mk_stmts_md [assign_uop left ToStringOp e])
                | ObjectType _
                | ReferenceType _ -> raise (Invalid_argument "To string prim cannot take objects and references as arguments") 
              end
            | TI_Value | TI_NotARef -> None
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to to_string_prim")
          end
      end
      
let simplify_to_string e sf_annot left throw_var label_throw =
  let annot = sf_annot.as_annot in 
  match e with
    | Literal (LLoc _) -> None
    | Literal Undefined | Literal Null | Literal (Bool _) | Literal (String _) | Literal (Num _) | Field _ | BinOp _ | UnaryOp _ -> simplify_to_string_prim e sf_annot left
    | Literal Empty | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "To string cannot take empty / type / typeof / ref as an argument") 
    | Base _ -> None
     | Var var -> 
      begin match get_type_info annot var with
        | None -> None
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType | UndefinedType | BooleanType | StringType | NumberType -> simplify_to_string_prim e sf_annot left
                | ObjectType _ -> None
                | ReferenceType _ -> raise (Invalid_argument "To_string cannot take and references as arguments") 
              end
            | TI_Value | TI_NotARef -> None
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to to_string")
          end
      end
      
let simplify_to_object e sf_annot left throw_var label_throw =
  let annot = sf_annot.as_annot in 
  let md = sf_annot.as_stmt.stmt_data in
  let mk_stmts_md = mk_stmts md in
  match e with
    | Literal (LLoc _) -> Some (mk_stmts_md [assign_expr left e])
    | Literal Undefined | Literal Null -> Some (translate_error_throw Ltep throw_var label_throw md)
    | Literal (Bool _) -> Some (make_builtin_call (Boolean_Construct) left None [e] throw_var label_throw md)
    | Literal (String _) | Field _ -> Some (make_builtin_call (String_Construct) left None [e] throw_var label_throw md)
    | Literal (Num _) -> Some (make_builtin_call (Number_Construct) left None [e] throw_var label_throw md)
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
                | NullType | UndefinedType -> Some (translate_error_throw Ltep throw_var label_throw md)
                | BooleanType -> Some (make_builtin_call (Boolean_Construct) left None [e] throw_var label_throw md)
                | StringType -> Some (make_builtin_call (String_Construct) left None [e] throw_var label_throw md)
                | NumberType -> Some (make_builtin_call (Number_Construct) left None [e] throw_var label_throw md)
                | ObjectType _ -> Some (mk_stmts_md [assign_expr left e])
                | ReferenceType _ -> raise (Invalid_argument "To_object cannot take and references as arguments") 
              end
            | TI_Value | TI_NotARef -> None
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to to_object")
          end
      end
      
let simplify_to_primitive e preftype sf_annot left throw_var label_throw =
  let annot = sf_annot.as_annot in 
  let md = sf_annot.as_stmt.stmt_data in
  let mk_stmts_md = mk_stmts md in
  match e with
    | Literal (LLoc _) -> None
    | Literal Undefined | Literal Null | Literal (Bool _) | Literal (String _) | Field _ | Literal (Num _) | BinOp _ | UnaryOp _ -> Some (mk_stmts_md [assign_expr left e])
    | Literal Empty | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "To object cannot take empty / type / typeof / ref as an argument") 
    | Base _ -> None
    | Var var -> 
      begin match get_type_info annot var with
        | None -> None
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType | UndefinedType | BooleanType | StringType | NumberType -> Some (mk_stmts_md [assign_expr left e])
                | ObjectType _ -> None
                | ReferenceType _ -> raise (Invalid_argument "To_primitive cannot take and references as arguments") 
              end
            | TI_Value | TI_NotARef -> None
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to to_primitive")
          end
      end
      
let simplify_strict_equality_comparison_types_equal e1 e2 sf_annot left =
  let annot = sf_annot.as_annot in 
  let md = sf_annot.as_stmt.stmt_data in
  let mk_stmts_md = mk_stmts md in
  match e1 with
    | Literal Undefined | Literal Null -> Some (mk_stmts_md [assign_true left])
    | Literal (LLoc _) | Literal (Bool _) | Literal (String _) | Field _ -> Some (translate_strict_equality_comparison_types_equal_if_equal e1 e2 left md) (* TODO: Do I really want to use field as String? *)
    | Literal (Num n1) ->
      begin
        match e2 with
          | Literal (Num n2) ->
            if (n1 = n2) (* nan != nan and TODO check: 0.0 == -0.0 *) then 
              Some (mk_stmts_md [assign_true left]) 
            else Some (mk_stmts_md [assign_false left])
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
                | NullType | UndefinedType -> Some (mk_stmts_md [assign_true left])
                | BooleanType | StringType | ObjectType _ -> Some (translate_strict_equality_comparison_types_equal_if_equal e1 e2 left md)
                | NumberType -> None               
                | ReferenceType _ -> raise (Invalid_argument "=== same types cannot take and references as arguments") 
              end
            | TI_Value | TI_NotARef -> None
            | TI_Empty -> raise (Invalid_argument "=== same types cannot be as an argument to IsCallable")
          end
      end
      
let simplify_strict_equality_comparison e1 e2 sf_annot left =
  let annot = sf_annot.as_annot in 
  let md = sf_annot.as_stmt.stmt_data in
  let mk_stmts_md = mk_stmts md in

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
            if t1 = t2 then simplify_strict_equality_comparison_types_equal e1 e2 sf_annot left
            else Some (mk_stmts_md [assign_false left])
        end
      end