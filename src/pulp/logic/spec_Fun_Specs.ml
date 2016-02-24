(* ./src/pulp/logic/spec_Fun_Specs.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open Pulp_Logic
open Pulp_Logic_Utils
open Pulp_Procedure
open Pulp_Syntax_Print
open Pulp_Syntax
open Pulp_Translate_Aux

let dummy_exp = (Literal Undefined)

let dummy_exp1 = (Literal Undefined)  

let dummy_exp2 = (Literal Undefined) 

let get_value_fn () = string_of_spec_fun_id (GetValue dummy_exp)

let get_value_not_a_ref_pre param = type_of_not_a_ref_f param

let get_value_unresolvable_ref_pre param = Star [
    type_of_ref_f param; 
    Eq (Le_Base param, Le_Literal Undefined)
  ]
  
let get_value_vref_obj_pre param v = Star [
    type_of_vref_f param;
    NEq (Le_Base param, Le_Literal (LLoc Lg));
    Heaplet (Le_Base param, Le_Field param, v);
    NEq (v, Le_None) 
  ]
  
let get_value_vref_lg param v = 
   let ls = Le_Var (fresh_e()) in
   let l = Le_Var (fresh_e()) in 
     combine
      (proto_pred_f ls (Le_Literal (LLoc Lg)) (Le_Field param) l v)
      (Star [
        type_of_vref_f param; 
        Eq (Le_Base param, Le_Literal (LLoc Lg));
        NEq (v, Le_Literal Empty) 
      ])
      
let get_value_mref_empty_pre param = 
   let ls = Le_Var (fresh_e()) in
   let l = Le_Var (fresh_e()) in 
     combine
     (proto_pred_f ls (Le_Base param) (Le_Field param) l (Le_Literal Empty))   
     (Star [
       type_of_mref_f param; 
       type_of_obj_f (Le_Base param)
     ])
    
let get_value_mref_not_empty_pre param v = 
   let ls = Le_Var (fresh_e()) in
   let l = Le_Var (fresh_e()) in 
     combine 
       (proto_pred_f ls (Le_Base param) (Le_Field param) l v)
       (Star [
         type_of_mref_f param; 
         type_of_obj_f (Le_Base param);
         NEq (v, Le_Literal Empty) 
       ])

let get_value_spec param ctx =
  let pre_not_a_ref = get_value_not_a_ref_pre (Le_PVar param) in
  
  let pre_unresolvable_ref = get_value_unresolvable_ref_pre (Le_PVar param) in
  
  let lerror = Le_Var (fresh_e()) in
  let post_unresolvable_ref = combine pre_unresolvable_ref
    (Star [
      REq lerror;
      proto_heaplet_f lerror (Le_Literal (LLoc Lrep));
      class_heaplet_f lerror "Error"
    ]) in
 
  let v1 = Le_Var (fresh_a()) in
  let pre_vref_obj = get_value_vref_obj_pre (Le_PVar param) v1 in 
  
  let v2 = Le_Var (fresh_a()) in
  let pre_vref_lg = get_value_vref_lg (Le_PVar param) v2  in
  
  let pre_mref_empty = get_value_mref_empty_pre (Le_PVar param) in
  
  let v3 = Le_Var (fresh_a()) in
  let pre_mref_not_empty = get_value_mref_not_empty_pre (Le_PVar param) v3 in
  
  [(mk_spec_with_excep pre_not_a_ref [combine pre_not_a_ref (REq (Le_PVar param))] [false_f]);
   (mk_spec_with_excep pre_unresolvable_ref [false_f] [post_unresolvable_ref]);
   (mk_spec_with_excep pre_vref_obj [combine pre_vref_obj (REq v1)] [false_f]);
   (mk_spec_with_excep pre_vref_lg [combine pre_vref_lg (REq v2)] [false_f]);
   (mk_spec_with_excep pre_mref_empty [combine pre_mref_empty (REq (Le_Literal Undefined))] [false_f]);
   (mk_spec_with_excep pre_mref_not_empty [combine pre_mref_not_empty (REq v3)] [false_f])
  ] 
  
let get_value_fb () =
  let param = "x" in
  let ctx = create_ctx [] in
  let bd = (translate_gamma (Var param) ctx.return_var ctx.throw_var ctx.label_throw) @
    [ Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw ] in
  let bd = to_ivl_goto bd in
  make_function_block_with_spec Procedure_Spec (get_value_fn()) bd [param] ctx (get_value_spec param ctx)

let make_put_value_function () = 
	let ctx = create_ctx [] in 
	let arg_var1 = fresh_r () in 
	let arg_var2 = fresh_r () in 
	let body = translate_put_value (Var arg_var1) (Var arg_var2) ctx.throw_var ctx.label_throw in 
	let body = body @
		[ 
			Basic (Assignment (mk_assign ctx.return_var (Expression (Literal Empty)))); 
			Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block Procedure_Spec (string_of_spec_fun_id (PutValue (dummy_exp1, dummy_exp2))) body [rthis; rscope; arg_var1; arg_var2] ctx

let make_get_function () = 
	let ctx = create_ctx [] in 
	let arg_obj = fresh_r () in 
	let arg_prop = fresh_r () in 
	let body = translate_get (Var arg_obj) (Var arg_prop) ctx.return_var in 
	let body = body @
		[ Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block Procedure_Spec (string_of_spec_fun_id (Get (dummy_exp1, dummy_exp2))) body [rthis; rscope; arg_obj; arg_prop] ctx 

let make_has_property_function () = 
	let ctx = create_ctx [] in 
	let arg_obj = fresh_r () in 
	let arg_prop = fresh_r () in 
	let body = translate_has_property (Var arg_obj) (Var arg_prop) ctx.return_var in 
	let body = body @
		[ Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block Procedure_Spec  (string_of_spec_fun_id (HasProperty (dummy_exp1, dummy_exp2))) body [rthis; rscope; arg_obj; arg_prop] ctx 						

let make_to_boolean_function () = 
	let ctx = create_ctx [] in 
	let arg = fresh_r () in 
	let body = translate_to_boolean (Var arg) ctx.return_var in 
	let body = body @
		[ Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block Procedure_Spec (string_of_spec_fun_id (ToBoolean dummy_exp1)) body [rthis; rscope; arg] ctx 	

let make_to_string_function () = 
	let ctx = create_ctx [] in 
	let arg = fresh_r () in 
	let body = translate_to_string (Var arg) ctx.return_var ctx.throw_var ctx.label_throw in 
	let body = body @
		[ Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block Procedure_Spec (string_of_spec_fun_id (ToString dummy_exp1)) body [rthis; rscope; arg] ctx 	

let make_to_string_prim_function () = 
	let ctx = create_ctx [] in 
	let arg = fresh_r () in 
	let body = translate_to_string_prim (Var arg) ctx.return_var in 
	let body = body @
		[ Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block Procedure_Spec (string_of_spec_fun_id (ToStringPrim dummy_exp1)) body [rthis; rscope; arg] ctx 	

let make_to_object_function () = 
	let ctx = create_ctx [] in 
	let arg = fresh_r () in 
	let body = translate_to_object (Var arg) ctx.return_var ctx.throw_var ctx.label_throw  in 
	let body = body @
		[ Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block Procedure_Spec (string_of_spec_fun_id (ToObject dummy_exp1)) body [rthis; rscope; arg] ctx 	

let make_check_object_coercible_function () = 
	let ctx = create_ctx [] in 
	let arg = fresh_r () in 
	let body = translate_obj_coercible (Var arg) ctx.throw_var ctx.label_throw  in 
	let body = body @
		[ Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block Procedure_Spec (string_of_spec_fun_id (CheckObjectCoercible dummy_exp1)) body [rthis; rscope; arg] ctx 	

let make_is_callable_function () = 
	let ctx = create_ctx [] in 
	let arg = fresh_r () in 
	let body = is_callable (Var arg) ctx.label_return  in 
	let body = body @
		[ Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block Procedure_Spec (string_of_spec_fun_id (IsCallable dummy_exp1)) body [rthis; rscope; arg] ctx 	

let make_strict_equality_function () = 
	let ctx = create_ctx [] in 
	let arg1 = fresh_r () in 
	let arg2 = fresh_r () in 
	let body = translate_strict_equality_comparison (Var arg1) (Var arg2) ctx.label_return  in 
	let body = body @
		[ Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block Procedure_Spec (string_of_spec_fun_id (StrictEquality (dummy_exp1, dummy_exp2))) body [rthis; rscope; arg1; arg2] ctx 	

let make_strict_equality_same_type_function () = 
	let ctx = create_ctx [] in 
	let arg1 = fresh_r () in 
	let arg2 = fresh_r () in 
	let body = translate_strict_equality_comparison_types_equal (Var arg1) (Var arg2) ctx.label_return  in 
	let body = body @
		[ Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block Procedure_Spec (string_of_spec_fun_id (StrictEqualitySameType (dummy_exp1, dummy_exp2))) body [rthis; rscope; arg1; arg2] ctx 	


let get_env_spec () = 
  let env = AllFunctions.add (get_value_fn()) (get_value_fb ()) (AllFunctions.empty) in
	let env = AllFunctions.add (string_of_spec_fun_id (PutValue (dummy_exp1, dummy_exp2))) (make_put_value_function()) env in 
	let env = AllFunctions.add (string_of_spec_fun_id (Get (dummy_exp1, dummy_exp2))) (make_get_function()) env in 
	let env = AllFunctions.add (string_of_spec_fun_id (HasProperty (dummy_exp1, dummy_exp2))) (make_has_property_function()) env in 
	let env = AllFunctions.add (string_of_spec_fun_id (ToBoolean dummy_exp1)) (make_to_boolean_function()) env in
	let env = AllFunctions.add (string_of_spec_fun_id (ToString dummy_exp1)) (make_to_string_function()) env in
	let env = AllFunctions.add (string_of_spec_fun_id (ToStringPrim dummy_exp1)) (make_to_string_prim_function()) env in
	let env = AllFunctions.add (string_of_spec_fun_id (ToObject dummy_exp1)) (make_to_object_function()) env in
	let env = AllFunctions.add (string_of_spec_fun_id (CheckObjectCoercible dummy_exp1)) (make_check_object_coercible_function()) env in
	let env = AllFunctions.add (string_of_spec_fun_id (IsCallable dummy_exp1)) (make_is_callable_function()) env in
	let env = AllFunctions.add (string_of_spec_fun_id (StrictEquality (dummy_exp1, dummy_exp2))) (make_strict_equality_function()) env in
	let env = AllFunctions.add (string_of_spec_fun_id (StrictEqualitySameType (dummy_exp1, dummy_exp2))) (make_strict_equality_same_type_function()) env in

  (* let env = Simp_Main.simplify env Simp_Common.Simp_Unfold_Specs in *) 
  env

  
  
