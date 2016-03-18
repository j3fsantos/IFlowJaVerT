(* ./src/pulp/simplifications/spec_Functions.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open Basic_Blocks
open Utils
open Pulp_Syntax
open Simp_Common
open Pulp_Procedure
open Control_Flow
open Pulp_Translate
open Type_Info
open Pulp_Translate_Aux

let simplify_get_value e left sf_annot throw_var label_throw =
  let annot = sf_annot.as_annot in 
  let md = sf_annot.as_stmt.stmt_data in
  let mk_stmts_md = mk_stmts md in
  let simplify_not_a_ref = mk_stmts_md [Basic (Assignment (mk_assign left (Expression e)))] in
  
  let simplify_ref_object e1 e1_ty e2 rt =
    match rt with
       | MemberReference ->  translate_gamma_member_reference_object e1 e2 left md
       | VariableReference ->
        begin match e1 with
           | Literal (LLoc Lg) -> translate_gamma_variable_reference_object_lg e1 e2 left md
           | Literal (LLoc _) ->  translate_gamma_variable_reference_object_not_lg e1 e2 left md
           | Literal _ | BinOp _ | UnaryOp _ | Base _ | Field _ | TypeOf _ | Ref _ ->  raise (Invalid_argument "Cannot Happen in simplify_ref_object") 
           | Var v ->
            begin match e1_ty with
              | Some Normal -> (* Definetely not Lg *) translate_gamma_variable_reference_object_not_lg e1 e2 left md
              | Some Builtin -> translate_gamma_variable_reference_object e1 e2 left md
              | None -> raise (Invalid_argument "Cannot Happen in simplify_ref_object for object type in get value")
            end 
        end
    in
    
  match e with
    | Literal _ | BinOp _ | UnaryOp _ | Base _ | Field _ | TypeOf _ -> simplify_not_a_ref
    | Var var -> 
      begin match get_type_info annot var with
        | None -> translate_gamma e left throw_var label_throw md
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType | UndefinedType | BooleanType | StringType | NumberType | ObjectType _ -> simplify_not_a_ref
                | ReferenceType _ -> translate_gamma_reference e left throw_var label_throw md 
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
            | Null ->  raise (Invalid_argument "Ref base cannot be null ")             
            | Bool _  | Num _  | String _ ->  translate_gamma_reference_prim_base e1 e2 left throw_var label_throw md
            | Undefined -> translate_error_throw Lrep throw_var label_throw md
            | Type pt -> raise (Invalid_argument "Type cannot be as an argument to Reference")
            | Empty -> raise (Invalid_argument "Empty cannot be as an argument to Reference")   
           end
        | BinOp _ 
        | UnaryOp _ -> (* TODO simplify more *) translate_gamma_reference e left throw_var label_throw md
        | Field _ -> translate_gamma_reference_prim_base e1 e2 left throw_var label_throw md (* Field (_) always return string *)
        | TypeOf _ -> raise (Invalid_argument "Not well formed expression Ref (BinOp | UnartOp | Field | TypeOf, _, _)") (* To introduce well formed expressions in normal form? *)
        | Base _ -> (* TODO *) translate_gamma_reference e left throw_var label_throw md (* if it's base of some variable and we know that variable is a type of member of object reference  *)
        | Var var ->        
	        begin match get_type_info annot var with
	          | None -> translate_gamma_reference_base_field e e1 e2 left throw_var label_throw md
	          | Some pt ->
	            begin match pt with
	              | TI_Type pt ->
	                begin match pt with
	                  | NullType -> raise (Invalid_argument "Ref base cannot be null ") 
	                  | UndefinedType -> translate_error_throw Lrep throw_var label_throw md
	                  | BooleanType | StringType | NumberType -> translate_gamma_reference_prim_base e1 e2 left throw_var label_throw md
	                  | ObjectType ot -> simplify_ref_object e1 ot e2 rt
	                  | ReferenceType _ -> raise (Invalid_argument "Reference cannot be as an argument to Reference") 
	                end
	              | TI_Value | TI_NotARef -> translate_gamma_reference_base_field e e1 e2 left throw_var label_throw md
	              | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to Reference")
	            end
	      end
        | Ref _ -> raise (Invalid_argument "Reference cannot be as an argument to Reference")
     end

let simplify_put_value e1 e2 sf_annot throw_var label_throw =
  let annot = sf_annot.as_annot in 
  let md = sf_annot.as_stmt.stmt_data in
  let gotothrow = translate_error_throw Lrep throw_var label_throw md in
    
  match e1 with
    | Literal _ | BinOp _ | UnaryOp _ | Base _ | Field _ | TypeOf _ -> gotothrow
    | Var var -> 
      begin match get_type_info annot var with
        | None -> translate_put_value e1 e2 throw_var label_throw md
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType | UndefinedType | BooleanType | StringType | NumberType | ObjectType _ -> gotothrow
                | ReferenceType _ ->  translate_put_value_reference e1 e2 throw_var label_throw md
              end
            | TI_Value | TI_NotARef -> gotothrow
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to get_value")
          end
      end
    | Ref (base, field, rt) -> 
      begin match base with
        | Literal lit ->
          begin match lit with
            | LLoc l -> translate_put_value_reference_object_base_field base field e2 md
            | Null ->  raise (Invalid_argument "Ref base cannot be null ")             
            | Bool _  | Num _  | String _ -> gotothrow
            | Undefined -> gotothrow
            | Type pt -> raise (Invalid_argument "Type cannot be as an argument to Reference")
            | Empty -> raise (Invalid_argument "Empty cannot be as an argument to Reference")   
           end
        | BinOp _ 
        | UnaryOp _ -> (* TODO simplify more *) translate_put_value_reference_base e1 base e2 throw_var label_throw md
        | Field _ -> gotothrow (* Field (_) always return string *)
        | TypeOf _ -> raise (Invalid_argument "Not well formed expression Ref (BinOp | UnartOp | Field | TypeOf, _, _)") (* To introduce well formed expressions in normal form? *)
        | Base _ -> (* TODO *) translate_put_value_reference e1 e2 throw_var label_throw md (* if it's base of some variable and we know that variable is a type of member of object reference  *)
        | Var var ->        
            begin match get_type_info annot var with
              | None -> translate_put_value_reference_base e1 base e2 throw_var label_throw md
              | Some pt ->
                begin match pt with
                  | TI_Type pt ->
                    begin match pt with
                      | NullType -> raise (Invalid_argument "Ref base cannot be null ") 
                      | UndefinedType -> gotothrow
                      | BooleanType | StringType | NumberType -> gotothrow
                      | ObjectType ot -> translate_put_value_reference_object_base_field base field e2 md
                      | ReferenceType _ -> raise (Invalid_argument "Reference cannot be as an argument to Reference") 
                    end
                  | TI_Value | TI_NotARef -> translate_put_value_reference_base e1 base e2 throw_var label_throw md
                  | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to Reference")
                end
          end
        | Ref _ -> raise (Invalid_argument "Reference cannot be as an argument to Reference")
     end
    
let simplify_to_boolean e sf_annot left =
  let annot = sf_annot.as_annot in 
  let md = sf_annot.as_stmt.stmt_data in
  let mk_stmts_md = mk_stmts md in
  match e with
    | Literal Undefined | Literal Null  | Literal (Bool false) | Literal (String "") | Literal (Num 0.0) -> mk_stmts_md [assign_false left] 
    | Literal (Num nan) -> mk_stmts_md [assign_false left] (* Why does it complain for nan? *)
    | Literal Empty | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "To boolean cannot take empty / type / typeof / ref as an argument") 
    | Literal _ | Field _ -> mk_stmts_md [assign_true left] (* Field cannot be empty *)
    | BinOp _ | UnaryOp _ | Base _ -> translate_to_boolean e left md
    | Var var -> 
      begin match get_type_info annot var with
        | None -> translate_to_boolean e left md
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType | UndefinedType -> mk_stmts_md [assign_false left]
                | BooleanType | StringType | NumberType -> translate_to_boolean e left md
                | ObjectType _ ->  mk_stmts_md [assign_true left]
                | ReferenceType _ -> raise (Invalid_argument "To boolean cannot take referece as an argument") 
              end
            | TI_Value | TI_NotARef -> translate_to_boolean e left md
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to to_boolean")
          end
      end
      
let simplify_to_number_prim e sf_annot left =
  let annot = sf_annot.as_annot in 
  let md = sf_annot.as_stmt.stmt_data in
  let mk_stmts_md = mk_stmts md in
  match e with
    | Literal Undefined -> mk_stmts_md [assign_num left nan]
    | Literal Null | Literal (Bool false) -> mk_stmts_md [assign_num left 0.0]
    | Literal (Bool true) -> mk_stmts_md [assign_num left 1.0]
    | Literal (String s) -> mk_stmts_md [assign_to_number left s] 
    | Literal (Num n) -> mk_stmts_md [assign_num left n]
    | Literal Empty | Literal (LLoc _) | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "To number prim cannot take empty / object / type / typeof / ref as an argument") 
    | Field _ -> mk_stmts_md [assign_uop left ToNumberOp e] (* Field return string *)
    | BinOp _ | UnaryOp _ | Base _ -> translate_to_number_prim e left md  (* TODO: Different types for different operators *)
    | Var var -> 
      begin match get_type_info annot var with
        | None -> translate_to_number_prim e left md
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType -> mk_stmts_md [assign_num left 0.0]
                | UndefinedType -> mk_stmts_md [assign_num left nan]
                | BooleanType -> translate_to_number_bool e left md
                | StringType -> mk_stmts_md [assign_uop left ToNumberOp e]
                | NumberType -> mk_stmts_md [assign_expr left e]
                | ObjectType _
                | ReferenceType _ -> raise (Invalid_argument "To number prim cannot take objects and references as arguments") 
              end
            | TI_Value | TI_NotARef -> translate_to_number_prim e left md
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to to_number_prim")
          end
      end
      
let simplify_to_number e sf_annot left throw_var label_throw =
  let annot = sf_annot.as_annot in 
  let md = sf_annot.as_stmt.stmt_data in
  match e with
    | Literal (LLoc _) -> translate_to_number_object e left throw_var label_throw md
    | Literal Undefined | Literal Null | Literal (Bool _) | Literal (String _) | Literal (Num _) | Field _ | BinOp _ | UnaryOp _ -> simplify_to_number_prim e sf_annot left
    | Literal Empty | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "To number cannot take empty / type / ref as an argument") 
    | Base _ -> translate_to_number e left throw_var label_throw md
    | Var var -> 
      begin match get_type_info annot var with
        | None -> translate_to_number e left throw_var label_throw md
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType | UndefinedType | BooleanType | StringType | NumberType -> simplify_to_number_prim e sf_annot left
                | ObjectType _ -> translate_to_number_object e left throw_var label_throw md
                | ReferenceType _ -> raise (Invalid_argument "To number cannot take and references as arguments") 
              end
            | TI_Value | TI_NotARef -> translate_to_number e left throw_var label_throw md
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to to_number")
          end
      end
      
let simplify_to_string_prim e sf_annot left =
  let annot = sf_annot.as_annot in 
  let md = sf_annot.as_stmt.stmt_data in
  let mk_stmts_md = mk_stmts md in
  match e with
    | Literal Undefined -> mk_stmts_md [assign_string left "undefined"]
    | Literal Null -> mk_stmts_md [assign_string left "null"]
    | Literal (Bool false) -> mk_stmts_md [assign_string left "false"]
    | Literal (Bool true) -> mk_stmts_md [assign_string left "true"]
    | Literal (String s) -> mk_stmts_md [assign_string left s] 
    | Literal (Num n) -> mk_stmts_md [assign_to_string left n]
    | Literal Empty | Literal (LLoc _) | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "To_string_prim cannot take empty / object / type / ref / base as an argument") 
    | Field _ -> mk_stmts_md [assign_expr left e] (* Field return string *)
    | BinOp _ | UnaryOp _  | Base _ -> translate_to_string_prim e left md (* TODO: Different types for different operators *)
    | Var var -> 
      begin match get_type_info annot var with
        | None -> translate_to_string_prim e left md
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType -> mk_stmts_md [assign_string left "null"]
                | UndefinedType -> mk_stmts_md [assign_string left "undefined"]
                | BooleanType -> translate_to_string_bool e left md
                | StringType -> mk_stmts_md [assign_expr left e]
                | NumberType -> mk_stmts_md [assign_uop left ToStringOp e]
                | ObjectType _
                | ReferenceType _ -> raise (Invalid_argument "To string prim cannot take objects and references as arguments") 
              end
            | TI_Value | TI_NotARef -> translate_to_string_prim e left md
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to to_string_prim")
          end
      end
      
let simplify_to_string e sf_annot left throw_var label_throw =
  let annot = sf_annot.as_annot in 
  let md = sf_annot.as_stmt.stmt_data in
  match e with
    | Literal (LLoc _) -> translate_to_string_object e left throw_var label_throw md
    | Literal Undefined | Literal Null | Literal (Bool _) | Literal (String _) | Literal (Num _) | Field _ | BinOp _ | UnaryOp _ -> simplify_to_string_prim e sf_annot left
    | Literal Empty | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "To string cannot take empty / type / typeof / ref as an argument") 
    | Base _ -> translate_to_string e left throw_var label_throw md
     | Var var -> 
      begin match get_type_info annot var with
        | None -> translate_to_string e left throw_var label_throw md
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType | UndefinedType | BooleanType | StringType | NumberType -> simplify_to_string_prim e sf_annot left
                | ObjectType _ -> translate_to_string_object e left throw_var label_throw md
                | ReferenceType _ -> raise (Invalid_argument "To_string cannot take and references as arguments") 
              end
            | TI_Value | TI_NotARef -> translate_to_string e left throw_var label_throw md
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to to_string")
          end
      end
      
let simplify_to_object e sf_annot left throw_var label_throw =
  let annot = sf_annot.as_annot in 
  let md = sf_annot.as_stmt.stmt_data in
  let mk_stmts_md = mk_stmts md in
  match e with
    | Literal (LLoc _) -> mk_stmts_md [assign_expr left e]
    | Literal Undefined | Literal Null -> translate_error_throw Ltep throw_var label_throw md
    | Literal (Bool _) -> make_builtin_call (Boolean_Construct) left None [e] throw_var label_throw md
    | Literal (String _) | Field _ -> make_builtin_call (String_Construct) left None [e] throw_var label_throw md
    | Literal (Num _) -> make_builtin_call (Number_Construct) left None [e] throw_var label_throw md
    | BinOp _ | UnaryOp _ -> translate_to_object_prim e left throw_var label_throw md (* TODO simplify more for the specific op *)
    | Literal Empty | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "To object cannot take empty / type / ref as an argument") 
    | Base _ -> translate_to_object e left throw_var label_throw md
    | Var var -> 
      begin match get_type_info annot var with
        | None -> translate_to_object e left throw_var label_throw md
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType | UndefinedType -> translate_error_throw Ltep throw_var label_throw md
                | BooleanType -> make_builtin_call (Boolean_Construct) left None [e] throw_var label_throw md
                | StringType -> make_builtin_call (String_Construct) left None [e] throw_var label_throw md
                | NumberType -> make_builtin_call (Number_Construct) left None [e] throw_var label_throw md
                | ObjectType _ -> mk_stmts_md [assign_expr left e]
                | ReferenceType _ -> raise (Invalid_argument "To_object cannot take and references as arguments") 
              end
            | TI_Value | TI_NotARef -> translate_to_object e left throw_var label_throw md
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to to_object")
          end
      end
      
let simplify_to_object_coercible e sf_annot throw_var label_throw =
  let annot = sf_annot.as_annot in 
  let md = sf_annot.as_stmt.stmt_data in
  match e with
    | Literal Undefined | Literal Null -> translate_error_throw Ltep throw_var label_throw md
    | Literal (Bool _) | Literal (String _) | Field _ | Literal (Num _) | BinOp _ | UnaryOp _ | Literal (LLoc _) -> []
    | Literal Empty | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "CheckObjectCoercible cannot take empty / type / typeof / ref as an argument") 
    | Base _ -> translate_obj_coercible e throw_var label_throw md
    | Var var -> 
      begin match get_type_info annot var with
        | None -> translate_obj_coercible e throw_var label_throw md
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType | UndefinedType -> translate_error_throw Ltep throw_var label_throw md
                | BooleanType | StringType | NumberType | ObjectType _ -> []
                | ReferenceType _ -> raise (Invalid_argument "CheckObjectCoercible cannot take and references as arguments") 
              end
            | TI_Value | TI_NotARef -> translate_obj_coercible e throw_var label_throw md
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to CheckObjectCoercible")
          end
      end
      
let simplify_to_primitive e preftype sf_annot left throw_var label_throw =
  let annot = sf_annot.as_annot in 
  let md = sf_annot.as_stmt.stmt_data in
  let mk_stmts_md = mk_stmts md in
  match e with
    | Literal (LLoc _) -> translate_default_value e preftype left throw_var label_throw md
    | Literal Undefined | Literal Null | Literal (Bool _) | Literal (String _) | Field _ | Literal (Num _) | BinOp _ | UnaryOp _ -> mk_stmts_md [assign_expr left e]
    | Literal Empty | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "To object cannot take empty / type / typeof / ref as an argument") 
    | Base _ -> translate_to_primitive e preftype left throw_var label_throw md
    | Var var -> 
      begin match get_type_info annot var with
        | None -> translate_to_primitive e preftype left throw_var label_throw md
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType | UndefinedType | BooleanType | StringType | NumberType -> mk_stmts_md [assign_expr left e]
                | ObjectType _ -> translate_default_value e preftype left throw_var label_throw md
                | ReferenceType _ -> raise (Invalid_argument "To_primitive cannot take and references as arguments") 
              end
            | TI_Value | TI_NotARef -> translate_to_primitive e preftype left throw_var label_throw md
            | TI_Empty -> raise (Invalid_argument "Empty cannot be as an argument to to_primitive")
          end
      end
      
let simplify_is_callable e sf_annot left =
  let annot = sf_annot.as_annot in 
  let md = sf_annot.as_stmt.stmt_data in
  let mk_stmts_md = mk_stmts md in
  match e with
    | Literal (LLoc _) -> is_callable_object e left md
    | Literal Undefined | Literal Null | Literal (Bool _) | Literal (String _) | Field _ | Literal (Num _) | BinOp _ | UnaryOp _ -> mk_stmts_md [assign_false left]
    | Literal Empty | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "IsCallable cannot take empty / type / typeof / ref as an argument") 
    | Base _ -> is_callable e left md
    | Var var -> 
      begin match get_type_info annot var with
        | None -> is_callable e left md
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType | UndefinedType | BooleanType | StringType | NumberType -> mk_stmts_md [assign_false left]
                | ObjectType _ -> is_callable_object e left md
                | ReferenceType _ -> raise (Invalid_argument "IsCallable cannot take and references as arguments") 
              end
            | TI_Value | TI_NotARef -> is_callable e left md
            | TI_Empty -> raise (Invalid_argument "IsCallable cannot be as an argument to IsCallable")
          end
      end
      
let simplify_strict_equality_comparison_types_equal e1 e2 sf_annot left =
  let annot = sf_annot.as_annot in 
  let md = sf_annot.as_stmt.stmt_data in
  let mk_stmts_md = mk_stmts md in
  match e1 with
    | Literal Undefined | Literal Null -> mk_stmts_md [assign_true left]
    | Literal (LLoc _) | Literal (Bool _) | Literal (String _) | Field _ -> translate_strict_equality_comparison_types_equal_if_equal e1 e2 left md (* TODO: Do I really want to use field as String? *)
    | Literal (Num n1) ->
      begin
        match e2 with
          | Literal (Num n2) ->
            if (n1 = n2) (* nan != nan and TODO check: 0.0 == -0.0 *) 
            then mk_stmts_md [assign_true left] 
            else mk_stmts_md [assign_false left]
          | _ -> translate_strict_equality_comparison_types_equal_number e1 e2 left md
      end
    | BinOp _ | UnaryOp _ | Base _ -> translate_strict_equality_comparison_types_equal e1 e2 left md
    | Literal Empty | Literal Type _ | TypeOf _ | Ref _ -> raise (Invalid_argument "=== same types cannot take empty / type / typeof / ref as an argument") 
    | Var var -> 
      begin match get_type_info annot var with
        | None -> translate_strict_equality_comparison_types_equal e1 e2 left md
        | Some pt ->
          begin match pt with
            | TI_Type pt ->
              begin match pt with
                | NullType | UndefinedType -> mk_stmts_md [assign_true left]
                | BooleanType | StringType | ObjectType _ -> translate_strict_equality_comparison_types_equal_if_equal e1 e2 left md
                | NumberType -> translate_strict_equality_comparison_types_equal_number e1 e2 left md              
                | ReferenceType _ -> raise (Invalid_argument "=== same types cannot take and references as arguments") 
              end
            | TI_Value | TI_NotARef -> translate_strict_equality_comparison_types_equal e1 e2 left md
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
    | _, None -> translate_strict_equality_comparison e1 e2 left md
    | Some t1, Some t2 ->
      begin
        let t1 = Type_Info.get_pulp_type t1 in
        let t2 = Type_Info.get_pulp_type t2 in
        begin match t1, t2 with
          | None, _
          | _, None -> translate_strict_equality_comparison e1 e2 left md
          | Some t1, Some t2 ->
            if t1 = t2 then simplify_strict_equality_comparison_types_equal e1 e2 sf_annot left
            else mk_stmts_md [assign_false left]
        end
      end
 
let simplify_spec_func_unfold sf left sf_annot throw_var label_throw =
  let md = sf_annot.as_stmt.stmt_data in
  match sf with
    | GetValue e -> simplify_get_value e left sf_annot throw_var label_throw
    | PutValue (e1, e2) -> simplify_put_value e1 e2 sf_annot throw_var label_throw
    | GetOwnPropertyDefault (e1, e2) -> translate_get_own_property_default e1 e2 left md (* TODO *)
    | GetOwnPropertyString (e1, e2) -> translate_get_own_property_string e1 e2 left throw_var label_throw md (* TODO *)
    | Get (e1, e2) -> translate_get e1 e2 left throw_var label_throw md (* No simplifications. Might change after we have getters/setters *)
    | GetDefault (e1, e2) -> translate_get_default e1 e2 left md (* TODO *)
    | GetFunction (e1, e2) -> translate_get_function e1 e2 left throw_var label_throw md (* TODO *)
    | HasProperty (e1, e2) -> translate_has_property e1 e2 left md (* No simplifications *)
    | DefaultValue (e, pt) -> translate_default_value e pt left throw_var label_throw md (* Cannot do simplifications at this time. But this exploads a lot. Possible simplifications with separation logic reasoning *)
    | ToPrimitive (e, pt) -> simplify_to_primitive e pt sf_annot left throw_var label_throw (* Cannot do more simplifications at this time. Depends on Default Value *)
    | ToBoolean e -> simplify_to_boolean e sf_annot left
    | ToNumber e -> simplify_to_number e sf_annot left throw_var label_throw
    | ToNumberPrim e -> simplify_to_number_prim e sf_annot left
    | ToString e -> simplify_to_string e sf_annot left throw_var label_throw
    | ToStringPrim e -> simplify_to_string_prim e sf_annot left 
    | ToObject e -> simplify_to_object e sf_annot left throw_var label_throw
    | CheckObjectCoercible e -> simplify_to_object_coercible e sf_annot throw_var label_throw
    | IsCallable e -> simplify_is_callable e sf_annot left
    | AbstractRelation (e1, e2, b) -> translate_abstract_relation e1 e2 b left throw_var label_throw md
    | StrictEquality (e1, e2) -> simplify_strict_equality_comparison e1 e2 sf_annot left
    | StrictEqualitySameType (e1, e2) -> simplify_strict_equality_comparison_types_equal e1 e2 sf_annot left

let simplify_spec_func sf left sf_annot throw_var label_throw =
  let md = sf_annot.as_stmt.stmt_data in
  match sf with
    | GetValue e -> Spec_Functions_Simp.simplify_get_value e left sf_annot throw_var label_throw
    | PutValue (e1, e2) -> Spec_Functions_Simp.simplify_put_value e1 e2 sf_annot throw_var label_throw
    | GetOwnPropertyDefault _
    | GetOwnPropertyString _
    | GetDefault _
    | GetFunction _ -> None (* TODO *)
    | Get (e1, e2) -> Some (translate_get e1 e2 left throw_var label_throw md) (* TODO. Might change after we have getters/setters *)
    | HasProperty (e1, e2) -> Some (translate_has_property e1 e2 left md) (* No simplifications *)
    | DefaultValue (e, pt) -> None (* Cannot do simplifications at this time. But this exploads a lot. Possible simplifications with separation logic reasoning *)
    | ToPrimitive (e, pt) -> None (* Cannot do more simplifications at this time. Depends on Default Value *)
    | ToBoolean e -> Some (simplify_to_boolean e sf_annot left)
    | ToNumber e -> Spec_Functions_Simp.simplify_to_number e sf_annot left throw_var label_throw
    | ToNumberPrim e -> Spec_Functions_Simp.simplify_to_number_prim e sf_annot left
    | ToString e -> Spec_Functions_Simp.simplify_to_string e sf_annot left throw_var label_throw
    | ToStringPrim e -> Spec_Functions_Simp.simplify_to_string_prim e sf_annot left
    | ToObject e -> Spec_Functions_Simp.simplify_to_object e sf_annot left throw_var label_throw
    | CheckObjectCoercible e -> Some (simplify_to_object_coercible e sf_annot throw_var label_throw)
    | IsCallable e -> Some (simplify_is_callable e sf_annot left)
    | AbstractRelation (e1, e2, b) -> None
    | StrictEquality (e1, e2) -> Spec_Functions_Simp.simplify_strict_equality_comparison e1 e2 sf_annot left
    | StrictEqualitySameType (e1, e2) -> Spec_Functions_Simp.simplify_strict_equality_comparison_types_equal e1 e2 sf_annot left


let simplify_spec_func_aux sf left sf_annot throw_var label_throw option =
  match option with
    | Simp_Unfold_Specs -> Some (simplify_spec_func_unfold sf left sf_annot throw_var label_throw)
    | Simp_Specs -> simplify_spec_func sf left sf_annot throw_var label_throw

let simplify_spec_func left sf_annot sf option =
  let ctx =  {
     env_vars = [];  (*unused*)
     return_var = left;
     throw_var = left;
     label_entry = "entry." ^ fresh_r (); 
     label_return = "return." ^ fresh_r (); 
     label_throw = "throw." ^ fresh_r (); 
     label_continue = [];  (*unused*)
     label_break = [];  (*unused*)
     stmt_return_var = fresh_r();  (*unused*)
	  } in
	  let throw_var = ctx.throw_var in
	  let label_throw = ctx.label_throw in
    let simplified = simplify_spec_func_aux sf left sf_annot throw_var label_throw option in
    match simplified with 
      | None -> None
      | Some body ->
	      let stmts = to_ivl_goto body in
	      let stmts = stmts @ mk_stmts sf_annot.as_stmt.stmt_data [Goto ctx.label_return; Label ctx.label_return; Label ctx.label_throw] in
	      (*Printf.printf "Simplified spec function %s : %s" (Pulp_Syntax_Print.string_of_spec_function sf) (Pulp_Syntax_Print.string_of_statement_list stmts);*)
      Some (make_function_block Procedure_Spec "" stmts [] ctx)
  

let transform_spec_funcs cfg sf_annot option = 
  match sf_annot.as_stmt.stmt_stx with
    (* Why excep_label isn't used? *)
    | Sugar (SpecFunction (left, sf, excep_label)) ->
      simplify_spec_func left sf_annot sf option

    | _ -> raise (Invalid_argument "Expected SpecFunction")

let inject_spec_func cfg fb n_normal n_excep =
  let fb_cfg = fb_to_cfg fb in
  let fb_cfg_bb = transform_to_basic_blocks_from_cfg fb_cfg fb.func_ctx in
  CFG_BB.inject_graph cfg fb_cfg_bb;
  print_cfg_bb_single fb_cfg_bb "test";
  
  let all_labels = get_block_labels cfg in
  let return_node = Hashtbl.find all_labels fb.func_ctx.label_return in
  let throw_node = Hashtbl.find all_labels fb.func_ctx.label_throw in
  
  (* connect inject subgraph *)
  connect_blocks cfg return_node n_normal;
  connect_blocks cfg throw_node n_excep;
  
  Hashtbl.find all_labels fb.func_ctx.label_entry

(* Assumptions -- spec functions last commands in the block*)
(* and that they have two outgoing edges *)
let simplify_spec_functions cfg option =
  let nodes = CFG_BB.nodes cfg in
  List.iter (fun n ->
    let stmts = CFG_BB.get_node_data cfg n in
    
    let rev_stmts = List.rev stmts in
    match rev_stmts with
      | [] -> raise (Invalid_argument "Statement list in basic block should not be empty")
      | ({as_stmt = {stmt_stx = Sugar (SpecFunction _)} as stx1} as s1) :: tail ->
        begin
          let succs = CFG_BB.succ cfg n in
          let n_normal, n_excep = match succs with
            | [succ1; succ2] -> 
              begin
                match CFG_BB.get_edge_data cfg n succ1, CFG_BB.get_edge_data cfg n succ2 with
                  | Edge_Normal, Edge_Excep -> succ1, succ2
                  | Edge_Excep, Edge_Normal -> succ2, succ1
                  | _ ->  raise (Invalid_argument "Spec Functions should have one normal and one exceptional successor")
              end
            | _ -> raise (Invalid_argument "Spec Functions should have two successors") in
          (* Entry node of the unfolded spec func control flow subgraph *)
          
          let simp_fb = transform_spec_funcs cfg s1 option in 
          
          match simp_fb with
            | None -> ()
            | Some fb ->

		          let n_normal_stmts = CFG_BB.get_node_data cfg n_normal in
		          CFG_BB.set_node_data cfg n_normal ((as_annot_stmt(mk_stmt stx1.stmt_data (Label (fresh_r())))) :: n_normal_stmts);
		          
		          CFG_BB.rm_edge cfg n n_normal;
		          CFG_BB.rm_edge cfg n n_excep;
		          
		          let entry_n = inject_spec_func cfg fb n_normal n_excep in
		          let entry_label, md = get_block_label cfg entry_n in
		          
		          let updated_stmts = List.rev ((as_annot_stmt(mk_stmt md (Goto entry_label))) :: tail) in
		          CFG_BB.set_node_data cfg n updated_stmts;
		          
		          CFG_BB.mk_edge cfg n entry_n Edge_Normal
          
        end
      | _ -> ()
    
  ) nodes