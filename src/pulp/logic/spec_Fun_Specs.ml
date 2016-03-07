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

let get_value_mref_empty_pre2 param1 param2 = 
   let ls = Le_Var (fresh_e()) in
   let l = Le_Var (fresh_e()) in 
     (combine
     	(proto_pred_f ls param1 param2 l (Le_Literal Empty)) 
		 	(type_of_obj_f param1))
    
let get_value_mref_not_empty_pre2 param1 param2 v = 
   let ls = Le_Var (fresh_e()) in
   let l = Le_Var (fresh_e()) in 
     combine 
       (proto_pred_f ls param1 param2 l v)
       (Star [
         type_of_obj_f param1;
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

let put_value_spec param1 param2 ctx =
	let lerror = Le_Var (fresh_e()) in
	
	let pre_not_a_ref = get_value_not_a_ref_pre (Le_PVar param1) in
	
	let post_not_a_ref = combine pre_not_a_ref
    (Star [
      REq lerror;
      proto_heaplet_f lerror (Le_Literal (LLoc Lrep));
      class_heaplet_f lerror "Error"
    ]) in
	
	let pre_unresolvable_ref = get_value_unresolvable_ref_pre (Le_PVar param1) in
	
  let post_unresolvable_ref = combine pre_unresolvable_ref
    (Star [
      REq lerror;
      proto_heaplet_f lerror (Le_Literal (LLoc Lrep));
      class_heaplet_f lerror "Error"
    ]) in
	
	let pre_ref_with_prim_base = type_of_obj_not_prim_f  (Le_Base (Le_PVar param1)) in 
	
	let post_ref_with_prim_base = combine pre_ref_with_prim_base
		(Star [
      REq lerror;
      proto_heaplet_f lerror (Le_Literal (LLoc Lrep));
      class_heaplet_f lerror "Error"
    ]) in
	
	let pre_number_base = combine 
		(type_of_ref_f (Le_PVar param1))
		(combine
			(NEq (Le_Base  (Le_PVar param1), Le_Literal Undefined)) 
			(type_of_f  (Le_Base (Le_PVar param1)) NumberType)) in 
	
	let post_number_base = combine pre_number_base 
		(Star [
      REq lerror;
      proto_heaplet_f lerror (Le_Literal (LLoc Lrep));
      class_heaplet_f lerror "Error"
    ]) in 
	
	let pre_string_base = combine 
		(type_of_ref_f (Le_PVar param1))
		(combine
			(NEq (Le_Base  (Le_PVar param1), Le_Literal Undefined)) 
			(type_of_f  (Le_Base (Le_PVar param1)) StringType)) in 
	
	let post_string_base = combine pre_string_base 
		(Star [
      REq lerror;
      proto_heaplet_f lerror (Le_Literal (LLoc Lrep));
      class_heaplet_f lerror "Error"
    ]) in 
	
	let pre_boolean_base = combine 
		(type_of_ref_f (Le_PVar param1))
		(combine
			(NEq (Le_Base  (Le_PVar param1), Le_Literal Undefined)) 
			(type_of_f  (Le_Base (Le_PVar param1)) BooleanType)) in 
	
	let post_boolean_base = combine pre_boolean_base 
		(Star [
      REq lerror;
      proto_heaplet_f lerror (Le_Literal (LLoc Lrep));
      class_heaplet_f lerror "Error"
    ]) in 
					
	let post_ref_with_prim_base = combine pre_ref_with_prim_base
		(Star [
      REq lerror;
      proto_heaplet_f lerror (Le_Literal (LLoc Lrep));
      class_heaplet_f lerror "Error"
    ]) in
	
	let is_writable_ref = combine 
		(type_of_ref_f (Le_PVar param1))
		(eq_true (Le_BinOp ((Le_TypeOf (Le_Base (Le_PVar param1))), (Comparison Equal), (Le_Literal (Type (ObjectType (Some Normal))))))) in 
	
	let v1 = Le_Var (fresh_a()) in
	
	let pre_valid_ref_for_put_value = combine is_writable_ref 
		(Heaplet ((Le_Base (Le_PVar param1)), (Le_Field (Le_PVar param1)), v1)) in 
	
	let post_valid_ref_for_put_value = combine is_writable_ref
		(Heaplet ((Le_Base (Le_PVar param1)), (Le_Field (Le_PVar param1)), (Le_PVar param2))) in 
	
		[
			(mk_spec_with_excep pre_not_a_ref [false_f] [post_not_a_ref]);
			(mk_spec_with_excep pre_unresolvable_ref [false_f] [post_unresolvable_ref]); 
			(mk_spec_with_excep pre_number_base [false_f] [post_number_base]); 
			(mk_spec_with_excep pre_string_base [false_f] [post_string_base]); 
			(mk_spec_with_excep pre_boolean_base [false_f] [post_boolean_base]); 
			(mk_spec_with_excep pre_valid_ref_for_put_value [post_valid_ref_for_put_value] [false_f]) 
		] 
		
let has_property_spec param1 param2 ctx =
	let pre_prop_not_defined = (get_value_mref_empty_pre2 (Le_PVar param1) (Le_PVar param2)) in 
	
	let post_prop_not_defined = combine pre_prop_not_defined (REq (Le_Literal (Bool false))) in
	
  let v1 = Le_Var (fresh_a()) in
	
	let pre_prop_defined = get_value_mref_not_empty_pre2 (Le_PVar param1) (Le_PVar param2) v1 in
	
	let post_prop_defined = combine pre_prop_defined (REq (Le_Literal (Bool true))) in
	 
	[
			(mk_spec_with_excep pre_prop_not_defined [post_prop_not_defined] [false_f]);
			(mk_spec_with_excep pre_prop_defined [post_prop_defined] [false_f])
	] 

(* toBoolean spec *)
let mk_precise_pure_spec input_var input_val output_val = 
	let pre_condition = Eq ((Le_PVar input_var), (Le_Literal input_val)) in 
	let post_condition = combine pre_condition (REq (Le_Literal output_val)) in 
		mk_spec_with_excep pre_condition [post_condition] [false_f]
				
let mk_list_of_precise_pure_specs input_var lst_input_output = 
	let rec mk_list_of_precise_pure_specs_iter lst_input_output cur_specs = 
		match lst_input_output with 
		| [] -> cur_specs 
		| (input_val, output_val) :: rest_lst_input_outpt -> 
			let new_spec = mk_precise_pure_spec input_var input_val output_val in 
				mk_list_of_precise_pure_specs_iter rest_lst_input_outpt (new_spec :: cur_specs) in 
	mk_list_of_precise_pure_specs_iter lst_input_output []
	
let mk_precise_neg_spec val_lst input_var output_val = 
	let rec mk_precond val_lst cur_formula = 
		begin 
		match val_lst with 
		| [] -> cur_formula 
		| hd :: rest -> let new_conjunct = NEq ((Le_PVar input_var), (Le_Literal hd)) in 
			  begin 
				mk_precond rest (combine cur_formula new_conjunct)
				end
		end in
	let pre_cond = mk_precond val_lst empty_f in 
	let post_cond = combine pre_cond (REq (Le_Literal output_val)) in 
		mk_spec_with_excep pre_cond [post_cond] [false_f]

let to_boolean_spec param ctx = 
	let lst_falsy_values = 
		[	Undefined; 
		  Null; 
		  (Bool false); 
		  (String ""); 
		  (Num (-0.)); 
		  (Num (0.)); 
		  (Num nan); ] in 
	let lst_falsy_values_paired_with_false = List.map (fun arg -> (arg,  (Bool false))) lst_falsy_values in 
		(mk_precise_neg_spec lst_falsy_values param (Bool true)) 
			:: (mk_list_of_precise_pure_specs param lst_falsy_values_paired_with_false)

let get_value_fb () =
  let param = fresh_r() in
  let ctx = create_ctx [] in
  let bd = (translate_gamma (Var param) ctx.return_var ctx.throw_var ctx.label_throw empty_metadata) @
    mk_stmts_empty_data [ 
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw ] in
  let bd = to_ivl_goto bd in
  make_function_block_with_spec Procedure_Spec (get_value_fn()) bd [param] ctx (get_value_spec param ctx)

let make_put_value_function () = 
	let ctx = create_ctx [] in 
	let arg_var1 = fresh_r () in 
	let arg_var2 = fresh_r () in 
	let body = translate_put_value (Var arg_var1) (Var arg_var2) ctx.throw_var ctx.label_throw empty_metadata in 
	let body = body @
		mk_stmts_empty_data [ 
			Basic (Assignment (mk_assign ctx.return_var (Expression (Literal Empty)))); 
			Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block_with_spec Procedure_Spec 
		(string_of_spec_fun_id (PutValue (dummy_exp1, dummy_exp2))) body [arg_var1; arg_var2] ctx  (put_value_spec arg_var1 arg_var2 ctx)

let make_get_function () = 
	let ctx = create_ctx [] in 
	let arg_obj = fresh_r () in 
	let arg_prop = fresh_r () in 
	let body = translate_get (Var arg_obj) (Var arg_prop) ctx.return_var empty_metadata in 
	let body = body @
		mk_stmts_empty_data [ Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block Procedure_Spec (string_of_spec_fun_id (Get (dummy_exp1, dummy_exp2))) body [rthis; rscope; arg_obj; arg_prop] ctx 

let make_has_property_function () = 
	let ctx = create_ctx [] in 
	let arg_obj = fresh_r () in 
	let arg_prop = fresh_r () in 
	let body = translate_has_property (Var arg_obj) (Var arg_prop) ctx.return_var empty_metadata in 
	let body = body @
		mk_stmts_empty_data [ Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block_with_spec Procedure_Spec  
		(string_of_spec_fun_id (HasProperty (dummy_exp1, dummy_exp2))) body [arg_obj; arg_prop] ctx (has_property_spec arg_obj arg_prop ctx)						

let make_to_boolean_function () = 
	let ctx = create_ctx [] in 
	let arg = fresh_r () in 
	let body = translate_to_boolean (Var arg) ctx.return_var empty_metadata in 
	let body = body @
		mk_stmts_empty_data [ Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block_with_spec Procedure_Spec 
		(string_of_spec_fun_id (ToBoolean dummy_exp1)) body [arg] ctx (to_boolean_spec arg ctx)

let make_to_string_function () = 
	let ctx = create_ctx [] in 
	let arg = fresh_r () in 
	let body = translate_to_string (Var arg) ctx.return_var ctx.throw_var ctx.label_throw empty_metadata in 
	let body = body @
		mk_stmts_empty_data [ Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block Procedure_Spec (string_of_spec_fun_id (ToString dummy_exp1)) body [rthis; rscope; arg] ctx 	

let make_to_string_prim_function () = 
	let ctx = create_ctx [] in 
	let arg = fresh_r () in 
	let body = translate_to_string_prim (Var arg) ctx.return_var empty_metadata in 
	let body = body @
		 mk_stmts_empty_data [ Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block Procedure_Spec (string_of_spec_fun_id (ToStringPrim dummy_exp1)) body [rthis; rscope; arg] ctx 	

let make_to_object_function () = 
	let ctx = create_ctx [] in 
	let arg = fresh_r () in 
	let body = translate_to_object (Var arg) ctx.return_var ctx.throw_var ctx.label_throw empty_metadata in 
	let body = body @
		mk_stmts_empty_data [ Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block Procedure_Spec (string_of_spec_fun_id (ToObject dummy_exp1)) body [rthis; rscope; arg] ctx 	

let make_check_object_coercible_function () = 
	let ctx = create_ctx [] in 
	let arg = fresh_r () in 
	let body = translate_obj_coercible (Var arg) ctx.throw_var ctx.label_throw empty_metadata in 
	let body = body @
		mk_stmts_empty_data [ Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block Procedure_Spec (string_of_spec_fun_id (CheckObjectCoercible dummy_exp1)) body [rthis; rscope; arg] ctx 	

let make_is_callable_function () = 
	let ctx = create_ctx [] in 
	let arg = fresh_r () in 
	let body = is_callable (Var arg) ctx.label_return empty_metadata in 
	let body = body @
		mk_stmts_empty_data [ Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block Procedure_Spec (string_of_spec_fun_id (IsCallable dummy_exp1)) body [rthis; rscope; arg] ctx 	

let make_strict_equality_function () = 
	let ctx = create_ctx [] in 
	let arg1 = fresh_r () in 
	let arg2 = fresh_r () in 
	let body = translate_strict_equality_comparison (Var arg1) (Var arg2) ctx.label_return empty_metadata in 
	let body = body @
		mk_stmts_empty_data [ Goto ctx.label_return;
    	Label ctx.label_return;
    	Label ctx.label_throw ] in 
	let body = to_ivl_goto_unfold body in 
	make_function_block Procedure_Spec (string_of_spec_fun_id (StrictEquality (dummy_exp1, dummy_exp2))) body [rthis; rscope; arg1; arg2] ctx 	

let make_strict_equality_same_type_function () = 
	let ctx = create_ctx [] in 
	let arg1 = fresh_r () in 
	let arg2 = fresh_r () in 
	let body = translate_strict_equality_comparison_types_equal (Var arg1) (Var arg2) ctx.label_return empty_metadata in 
	let body = body @
		mk_stmts_empty_data [ Goto ctx.label_return;
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

  
  
