(* ./src/pulp/syntax/environment.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open Pulp_Syntax
open Pulp_Syntax_Print
open Pulp_Procedure
open Pulp_Translate_Aux
open Pulp_Logic
open Pulp_Logic_Utils

let builtin_call_boolean_call () =
  let v = fresh_r () in
  let ctx = create_ctx [] in
  let stmts, r1 = spec_func_call (ToBoolean (Var v)) ctx in
  let body = to_ivl_goto_unfold (* TODO translation level *)
    [ Sugar (If (equal_empty_expr (Var v),
       [ assign_false r1 ],
       stmts));
			assign_expr ctx.return_var (Var r1);
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block Procedure_Builtin (string_of_builtin_function Boolean_Call) body [rthis; rscope; v] ctx
  
let builtin_call_boolean_construct () =
  let v = fresh_r () in
  let ctx = create_ctx [] in
  let new_obj = mk_assign_fresh Obj in
  let stmts, r1 = spec_func_call (ToBoolean (Var v)) ctx in
  let body = to_ivl_goto_unfold (* TODO translation level *)
    [ Basic (Assignment new_obj);
      add_proto_value new_obj.assign_left Lbp;
      Basic (Mutation (mk_mutation (Var new_obj.assign_left) (literal_builtin_field FClass) (Literal (String "Boolean"))));
      Sugar (If (equal_empty_expr (Var v),
       [ Basic (Assignment (mk_assign r1 (Expression (Literal (Bool false)))))],
       stmts));
      Basic (Mutation (mk_mutation (Var new_obj.assign_left) (literal_builtin_field FPrimitiveValue) (Var r1)));
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var new_obj.assign_left))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in  
  let pre = type_of_f (Le_PVar v) BooleanType in
  let new_obj = Le_Var (fresh_e()) in  
  let post = [Star [
    REq new_obj;
    ObjFootprint (new_obj, [Le_Literal (String (string_of_builtin_field FProto)); Le_Literal (String (string_of_builtin_field FClass)); Le_Literal (String (string_of_builtin_field FPrimitiveValue))]);
    proto_heaplet_f new_obj (Le_Literal (LLoc Lbp));
    class_heaplet_f new_obj "Boolean";
    primitive_value_heaplet_f new_obj (Le_PVar v);
  ]] in
  let spec = [mk_spec_with_excep pre post []] in  
  make_function_block_with_spec Procedure_Builtin (string_of_builtin_function Boolean_Construct) body [rthis; rscope; v] ctx spec
  
let lbp_common ctx =
  let b = fresh_r () in
  let assign_b e = Basic (Assignment (mk_assign b (Expression e))) in  
  let class_lookup = mk_assign_fresh (Lookup (Var rthis, literal_builtin_field FClass)) in
  let prim_value = mk_assign_fresh (Lookup (Var rthis, literal_builtin_field FPrimitiveValue)) in
  Sugar (If (type_of_exp (Var rthis) BooleanType,
        [ assign_b (Var rthis)],
        [ Sugar (If (type_of_exp (Var rthis) (ObjectType None),
            [ 
              Basic (Assignment class_lookup);
              Sugar (If (equal_string_expr (Var class_lookup.assign_left) "Boolean",
                [ Basic (Assignment prim_value);
                  assign_b (Var prim_value.assign_left)
                ],
                translate_error_throw Ltep ctx.throw_var ctx.label_throw))
            ],
            translate_error_throw Ltep ctx.throw_var ctx.label_throw))
        ])), b
  
let builtin_lbp_toString () =
  let ctx = create_ctx [] in
  let rv = fresh_r () in
  let assign_rv rv e = Basic (Assignment (mk_assign rv (Expression e))) in  
  let stmt, b = lbp_common ctx in
  let body = to_ivl_goto_unfold (* TODO translation level *)
    [ stmt;
      Sugar (If (equal_bool_expr (Var b) true,
        [assign_rv rv (Literal (String "true"))],
        [assign_rv rv (Literal (String "false"))]));
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var rv))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block Procedure_Builtin (string_of_builtin_function Boolean_Prototype_toString) body [rthis; rscope] ctx
  
let builtin_lbp_valueOf () =
  let ctx = create_ctx [] in
  let stmt, b = lbp_common ctx in
  let body = to_ivl_goto_unfold (* TODO translation level *)
    [ stmt;
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var b))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block Procedure_Builtin (string_of_builtin_function Boolean_Prototype_valueOf) body [rthis; rscope] ctx
  
let builtin_lop_toString () =
  let ctx = create_ctx [] in
  let rv = fresh_r () in
  let assign_rv e = Basic (Assignment (mk_assign rv (Expression e))) in  
  let to_object, r1 = spec_func_call (ToObject (Var rthis)) ctx in
  let class_lookup = mk_assign_fresh (Lookup (Var r1, literal_builtin_field FClass)) in
  let body = to_ivl_goto_unfold (* TODO translation level *)
    [ Sugar (If (equal_undef_expr (Var rthis),
        [ assign_rv (Literal (String "[object Undefined]"))],
        [ Sugar (If (equal_null_expr (Var rthis),
            [ assign_rv (Literal (String "[object Null]"))],
            to_object @
            [
              Basic (Assignment class_lookup);
              assign_rv (concat_exprs (concat_exprs (Literal (String "[object ")) (Var class_lookup.assign_left)) (Literal (String "]")));
              ]))
        ]));
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var rv))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block Procedure_Builtin (string_of_builtin_function Object_Prototype_toString) body [rthis; rscope] ctx
  
let builtin_lop_valueOf () =
  let ctx = create_ctx [] in
  let to_object, r1 = spec_func_call (ToObject (Var rthis)) ctx in
  let body = to_ivl_goto_unfold (* TODO translation level *)
    to_object @
    [
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var r1))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block Procedure_Builtin (string_of_builtin_function Object_Prototype_valueOf) body [rthis; rscope] ctx
  
(* TODO fix empty value issue in other built-in function too. *)  
let builtin_object_construct () =
  let v = fresh_r () in
  let ctx = create_ctx [] in
  let rv = fresh_r () in
  let assign_rv e = Basic (Assignment (mk_assign rv (Expression e))) in  
  let stmts, r1 = spec_func_call (ToObject (Var v)) ctx in
  let new_obj = mk_assign_fresh Obj in
  let label_create = fresh_r () in
  let body = to_ivl_goto_unfold (* TODO translation level *)
    [ Sugar (If (equal_empty_expr (Var v), 
      [ Goto label_create ], 
        [ Sugar (If (type_of_exp (Var v) (ObjectType None),
            [assign_rv (Var v)],
            [ Sugar (If (istypeof_prim_expr (Var v),
              stmts @ 
              [ assign_rv (Var r1) ],
              [ Label label_create;
              Basic (Assignment new_obj);
                add_proto_value new_obj.assign_left Lop;
                Basic (Mutation (mk_mutation (Var new_obj.assign_left) (literal_builtin_field FClass) (Literal (String "Object"))));
                assign_rv (Var new_obj.assign_left)
              ]))
            ]))]));
          Basic (Assignment (mk_assign ctx.return_var (Expression (Var rv))));
          Goto ctx.label_return; 
          Label ctx.label_return; 
          Label ctx.label_throw
        ] in    
  let pre = Eq (Le_PVar v, Le_Literal (Empty)) in
  let new_obj = Le_Var (fresh_e()) in
  let post = [Star [
    REq new_obj;
    ObjFootprint (new_obj, [Le_Literal (String (string_of_builtin_field FProto)); Le_Literal (String (string_of_builtin_field FClass))]);
    proto_heaplet_f new_obj (Le_Literal (LLoc Lop));
    class_heaplet_f new_obj "Object";
  ]] in
  let spec = [mk_spec_with_excep pre post []] in
  make_function_block_with_spec Procedure_Builtin (string_of_builtin_function Object_Construct) body [rthis; rscope; v] ctx spec
  
let builtin_object_call () =
  let v = fresh_r () in
  let ctx = create_ctx [] in
  let rv = fresh_r () in
  let assign_rv e = Basic (Assignment (mk_assign rv (Expression e))) in  
  let stmts, r1 = spec_func_call (ToObject (Var v)) ctx in
  let new_obj = mk_assign_fresh Obj in
  let body = to_ivl_goto_unfold (* TODO translation level *)
    [ Sugar (If (or_expr 
                   (equal_empty_expr (Var v))
                   (or_expr (equal_undef_expr (Var v)) (equal_null_expr (Var v))),
        [ Basic (Assignment new_obj); (* TODO to make this a function for Object(), new Object(), Object literal *)
          add_proto_value new_obj.assign_left Lop;
          Basic (Mutation (mk_mutation (Var new_obj.assign_left) (literal_builtin_field FClass) (Literal (String "Object"))));
          assign_rv (Var new_obj.assign_left)
        ],
        stmts @
        [ assign_rv (Var r1)]));
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var rv))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block Procedure_Builtin (string_of_builtin_function Object_Call) body [rthis; rscope; v] ctx
  
let builtin_object_get_prototype_of () =
  let v = fresh_r () in
  let ctx = create_ctx [] in
  let body = to_ivl_goto_unfold (* TODO translation level *)
    [ Sugar (If (equal_empty_expr (Var v),
       translate_error_throw Ltep ctx.throw_var ctx.label_throw,
        [ Sugar (If (type_of_exp (Var v) (ObjectType None),
          [ Basic (Assignment (mk_assign ctx.return_var (Lookup (Var v, literal_builtin_field FProto))))],
          translate_error_throw Ltep ctx.throw_var ctx.label_throw))
        ])) ] @
     [ Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw 
    ] in    
  make_function_block Procedure_Builtin (string_of_builtin_function Object_getPrototypeOf) body [rthis; rscope; v] ctx
  
let builtin_lop_is_prototype_of () =
  let v = fresh_r () in
  let ctx = create_ctx [] in
  let to_obj_stmts, o = spec_func_call (ToObject (Var rthis)) ctx in
  let proto = mk_assign_fresh (Lookup (Var v, literal_builtin_field FProto)) in
  let proto_o = mk_assign_fresh (ProtoO (Var proto.assign_left, Var o)) in
  let body = to_ivl_goto_unfold (* TODO translation level *)
    [ Sugar (If (type_of_exp (Var v) (ObjectType None), 
          to_obj_stmts @
        [
          Basic (Assignment proto);
            Basic (Assignment proto_o);
            Basic (Assignment (mk_assign ctx.return_var (Expression (Var proto_o.assign_left))))
          ],
          [Basic (Assignment (mk_assign ctx.return_var (Expression (Literal (Bool false)))))]));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block Procedure_Builtin (string_of_builtin_function Object_Prototype_isPrototypeOf) body [rthis; rscope; v] ctx
  
let builtin_lfp_call () = 
  let ctx = create_ctx [] in
  let body = to_ivl_goto_unfold (* TODO translation level *)
    ([ 
      Basic (Assignment (mk_assign ctx.return_var (Expression (Literal Undefined))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ]) in    
  make_function_block Procedure_Builtin (string_of_builtin_function Function_Call) body [rthis; rscope] ctx

let builtin_call_number_call () =
  let v = fresh_r () in
  let ctx = create_ctx [] in
  let stmts, r1 = spec_func_call (ToNumber (Var v)) ctx in 
  let body = to_ivl_goto_unfold (* TODO translation level *)
    ([ 
      Sugar (If (equal_empty_expr (Var v),
        [ Basic (Assignment (mk_assign ctx.return_var (Expression (Literal (Num 0.)))))],
        stmts @ 
        [ Basic (Assignment (mk_assign ctx.return_var (Expression (Var r1))))]));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ]) in    
  make_function_block Procedure_Builtin (string_of_builtin_function Number_Call) body [rthis; rscope; v] ctx
  
let builtin_call_number_construct () =
  let v = fresh_r () in
  let ctx = create_ctx [] in
  let new_obj = mk_assign_fresh Obj in
  let stmts, r1 = spec_func_call (ToNumber (Var v)) ctx in
  let body = to_ivl_goto_unfold (* TODO translation level *)
    ([ Basic (Assignment new_obj);
       add_proto_value new_obj.assign_left Lnp;
       Basic (Mutation (mk_mutation (Var new_obj.assign_left) (literal_builtin_field FClass) (Literal (String "Number"))));
       Sugar (If (equal_empty_expr (Var v),
         [ Basic (Assignment (mk_assign r1 (Expression (Literal (Num 0.)))))],
         stmts));
       Basic (Mutation (mk_mutation (Var new_obj.assign_left) (literal_builtin_field FPrimitiveValue) (Var r1)));
       Basic (Assignment (mk_assign ctx.return_var (Expression (Var new_obj.assign_left))));
       Goto ctx.label_return; 
       Label ctx.label_return; 
       Label ctx.label_throw
     ]) in    
  make_function_block Procedure_Builtin (string_of_builtin_function Number_Construct) body [rthis; rscope; v] ctx
  
let lnp_common ctx =
  let b = fresh_r () in
  let assign_b e = Basic (Assignment (mk_assign b (Expression e))) in  
  let class_lookup = mk_assign_fresh (Lookup (Var rthis, literal_builtin_field FClass)) in
  let prim_value = mk_assign_fresh (Lookup (Var rthis, literal_builtin_field FPrimitiveValue)) in
  Sugar (If (type_of_exp (Var rthis) NumberType,
        [ assign_b (Var rthis)],
        [ Sugar (If (type_of_exp (Var rthis) (ObjectType None),
            [ 
              Basic (Assignment class_lookup);
              Sugar (If (equal_string_expr (Var class_lookup.assign_left) "Number",
                [ Basic (Assignment prim_value);
                  assign_b (Var prim_value.assign_left)
                ],
                translate_error_throw Ltep ctx.throw_var ctx.label_throw))
            ],
            translate_error_throw Ltep ctx.throw_var ctx.label_throw))
        ])), b
  
let builtin_lnp_toString () = (* Todo for other redices too *)
  let ctx = create_ctx [] in
  let rv = fresh_r () in
  let assign_rv rv e = Basic (Assignment (mk_assign rv (Expression e))) in  
  let stmt, b = lnp_common ctx in
  let body = to_ivl_goto_unfold (* TODO translation level *)
    [ stmt;
      assign_rv rv (UnaryOp (ToStringOp, Var b));
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var rv))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block Procedure_Builtin (string_of_builtin_function Number_Prototype_toString) body [rthis; rscope] ctx
    
let builtin_lnp_valueOf () =
  let ctx = create_ctx [] in
  let stmt, b = lnp_common ctx in
  let body = to_ivl_goto_unfold (* TODO translation level *)
    [ stmt;
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var b))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block Procedure_Builtin (string_of_builtin_function Number_Prototype_valueOf) body [rthis; rscope] ctx
  
let builtin_global_is_nan () =
  let n = fresh_r () in
  let ctx = create_ctx [] in
  let stmts, r1 = spec_func_call (ToNumber (Var n)) ctx in 
  let body = to_ivl_goto_unfold (* TODO translation level *)
    (stmts @
    [ Sugar (If (equal_num_expr (Var r1) nan,
       [ Basic (Assignment (mk_assign ctx.return_var (Expression (Literal (Bool true)))))],
       [ Basic (Assignment (mk_assign ctx.return_var (Expression (Literal (Bool false)))))]
      ));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ]) in    
  make_function_block Procedure_Builtin (string_of_builtin_function Global_isNaN) body [rthis; rscope; n] ctx
  
let builtin_global_is_finite () =
  let n = fresh_r () in
  let ctx = create_ctx [] in
  let stmts, r1 = spec_func_call (ToNumber (Var n)) ctx in 
  let body = to_ivl_goto_unfold (* TODO translation level *)
    (stmts @
    [ Sugar (If (or_expr 
                  (equal_num_expr (Var r1) nan)
                  (or_expr 
                    (equal_num_expr (Var r1) infinity) 
                    (equal_num_expr (Var r1) neg_infinity)),
       [ Basic (Assignment (mk_assign ctx.return_var (Expression (Literal (Bool false)))))],
       [ Basic (Assignment (mk_assign ctx.return_var (Expression (Literal (Bool true)))))]
      ));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ]) in    
  make_function_block Procedure_Builtin (string_of_builtin_function Global_isFinite) body [rthis; rscope; n] ctx
  
let builtin_call_string_call () =
  let v = fresh_r () in
  let ctx = create_ctx [] in
  let stmts, r1 = spec_func_call (ToString (Var v)) ctx in 
  let body = to_ivl_goto_unfold (* TODO translation level *)
   [ Sugar (If (equal_empty_expr (Var v),
       [ Basic (Assignment (mk_assign r1 (Expression (Literal (String "")))))],
       stmts));
     Basic (Assignment (mk_assign ctx.return_var (Expression (Var r1))));
     Goto ctx.label_return; 
     Label ctx.label_return; 
     Label ctx.label_throw
    ] in    
  make_function_block Procedure_Builtin (string_of_builtin_function String_Call) body [rthis; rscope; v] ctx
  
let builtin_call_string_construct () =
  let v = fresh_r () in
  let ctx = create_ctx [] in
  let new_obj = mk_assign_fresh Obj in
  let stmts, r1 = spec_func_call (ToString (Var v)) ctx in 
  let body = to_ivl_goto_unfold (* TODO translation level *)
    ([ Basic (Assignment new_obj);
      add_proto_value new_obj.assign_left Lsp;
      Basic (Mutation (mk_mutation (Var new_obj.assign_left) (literal_builtin_field FClass) (Literal (String "String")))); 
      Sugar (If (equal_empty_expr (Var v),
       [ Basic (Assignment (mk_assign r1 (Expression (Literal (String "")))))],
       stmts));
      Basic (Mutation (mk_mutation (Var new_obj.assign_left) (literal_builtin_field FPrimitiveValue) (Var r1)));
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var new_obj.assign_left))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ]) in    
  let pre = type_of_f (Le_PVar v) StringType in
  let new_obj = Le_Var (fresh_e()) in  
  let post = [Star [
    REq new_obj;
    ObjFootprint (new_obj, [Le_Literal (String (string_of_builtin_field FProto)); Le_Literal (String (string_of_builtin_field FClass)); Le_Literal (String (string_of_builtin_field FPrimitiveValue))]);
    proto_heaplet_f new_obj (Le_Literal (LLoc Lsp));
    class_heaplet_f new_obj "String";
    primitive_value_heaplet_f new_obj (Le_PVar v);
  ]] in
  let spec = [mk_spec_with_excep pre post []] in 
  make_function_block_with_spec Procedure_Builtin (string_of_builtin_function String_Construct) body [rthis; rscope; v] ctx spec
    
let builtin_lsp_toString_valueOf () =
  let ctx = create_ctx [] in
  let b = fresh_r () in
  let assign_b e = Basic (Assignment (mk_assign b (Expression e))) in  
  let class_lookup = mk_assign_fresh (Lookup (Var rthis, literal_builtin_field FClass)) in
  let prim_value = mk_assign_fresh (Lookup (Var rthis, literal_builtin_field FPrimitiveValue)) in
  let body = to_ivl_goto_unfold (* TODO translation level *)
    [ Sugar (If (type_of_exp (Var rthis) StringType,
        [ assign_b (Var rthis)],
        [ Sugar (If (type_of_exp (Var rthis) (ObjectType None),
            [ 
              Basic (Assignment class_lookup);
              Sugar (If (equal_string_expr (Var class_lookup.assign_left) "String",
                [ Basic (Assignment prim_value);
                  assign_b (Var prim_value.assign_left)
                ],
                translate_error_throw Ltep ctx.throw_var ctx.label_throw));
            ],
            translate_error_throw Ltep ctx.throw_var ctx.label_throw))
        ]));
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var b))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block Procedure_Builtin (string_of_builtin_function String_Prototype_valueOf) body [rthis; rscope] ctx

let builtin_error_construct_call errorp func () =
  let message = fresh_r () in
  let ctx = create_ctx [] in
  let new_obj = mk_assign_fresh Obj in
  let stmts, m1 = spec_func_call (ToString (Var message)) ctx in
  let body = to_ivl_goto_unfold [
    Basic (Assignment new_obj);
    add_proto_value new_obj.assign_left errorp;
    Basic (Mutation (mk_mutation (Var new_obj.assign_left) (literal_builtin_field FClass) (Literal (String "Error"))));
    Sugar (If (equal_empty_expr (Var message),
      [],
      stmts @ [Basic (Mutation (mk_mutation (Var new_obj.assign_left) (Literal (String "message")) (Var m1)))]
    ));
    Basic (Assignment (mk_assign ctx.return_var (Expression (Var new_obj.assign_left))));
    Goto ctx.label_return;
    Label ctx.label_return;
    Label ctx.label_throw
  ] in
  make_function_block Procedure_Builtin (string_of_builtin_function func) body [rthis; rscope; message] ctx


let get_env () =
  let context_builtins = AllFunctions.empty in
	(*builtin functions*)
  let context_builtins = AllFunctions.add (string_of_builtin_function Boolean_Call) (builtin_call_boolean_call()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function Boolean_Construct) (builtin_call_boolean_construct()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function Boolean_Prototype_toString) (builtin_lbp_toString()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function Boolean_Prototype_valueOf) (builtin_lbp_valueOf()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function Object_Prototype_toString) (builtin_lop_toString()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function Object_Prototype_valueOf) (builtin_lop_valueOf()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function Object_Prototype_isPrototypeOf) (builtin_lop_is_prototype_of()) context_builtins in 
  let context_builtins = AllFunctions.add (string_of_builtin_function Object_Construct) (builtin_object_construct()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function Object_Call) (builtin_object_call()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function Object_getPrototypeOf) (builtin_object_get_prototype_of()) context_builtins in  
  let context_builtins = AllFunctions.add (string_of_builtin_function Number_Call) (builtin_call_number_call()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function Number_Construct) (builtin_call_number_construct()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function Number_Prototype_toString) (builtin_lnp_toString()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function Number_Prototype_valueOf) (builtin_lnp_valueOf()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function String_Call) (builtin_call_string_call()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function String_Construct) (builtin_call_string_construct()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function String_Prototype_toString) (builtin_lsp_toString_valueOf()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function String_Prototype_valueOf) (builtin_lsp_toString_valueOf()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function Function_Prototype_Call) (builtin_lfp_call()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function Global_isNaN) (builtin_global_is_nan()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function Global_isFinite) (builtin_global_is_finite()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function Error_Call_Construct) (builtin_error_construct_call Lep Error_Call_Construct ()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function TypeError_Call_Construct) (builtin_error_construct_call Ltep TypeError_Call_Construct ()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function ReferenceError_Call_Construct) (builtin_error_construct_call Lrep ReferenceError_Call_Construct ()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function SyntaxError_Call_Construct) (builtin_error_construct_call Lsep SyntaxError_Call_Construct ()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function EvalError_Call_Construct) (builtin_error_construct_call LEvalErrorP EvalError_Call_Construct ()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function RangeError_Call_Construct) (builtin_error_construct_call LRangeErrorP RangeError_Call_Construct ()) context_builtins in
  let context_builtins = AllFunctions.add (string_of_builtin_function URIError_Call_Construct) (builtin_error_construct_call LURIErrorP URIError_Call_Construct ()) context_builtins in
	
	context_builtins
