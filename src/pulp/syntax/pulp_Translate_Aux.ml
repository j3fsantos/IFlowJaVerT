(* ./src/pulp/syntax/pulp_Translate_Aux.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open Pulp_Syntax
open Pulp_Procedure
open Pulp_Syntax_Print

let or_expr e1 e2 = BinOp (e1, Boolean Or, e2)
let and_expr e1 e2 = BinOp (e1, Boolean And, e2)
let not_expr e1 = UnaryOp (Not, e1)
let equal_exprs e1 e2 = BinOp (e1, Comparison Equal, e2)
 
let concat_exprs e1 e2 = BinOp (e1, Concat, e2)
 
let type_of_exp e t = 
  let typeof = TypeOf e in
  let typelit = Literal (Type t) in
  match t with
    | ObjectType None
    | ReferenceType None -> (BinOp (typeof, Subtype, typelit)) 
    | NullType
    | UndefinedType
    | NumberType
    | StringType
    | BooleanType 
    | ObjectType _
    | ReferenceType _ -> BinOp (typeof, Comparison Equal, typelit)
    
let type_of_oref ref = type_of_exp ref (ReferenceType (Some MemberReference))
let type_of_vref ref = type_of_exp ref (ReferenceType (Some VariableReference))
let type_of_ref ref = type_of_exp ref (ReferenceType None)

let type_of_obj obj = type_of_exp obj (ObjectType None)
  
let istypeof_prim_expr v =
  or_expr 
  (type_of_exp v BooleanType)
  (or_expr 
     (type_of_exp v NumberType)
     (type_of_exp v StringType))
    
let is_prim_value v =
  or_expr 
  (type_of_exp v UndefinedType)
  (or_expr 
    (type_of_exp v NullType)
    (istypeof_prim_expr v)
  )  
    
        
let equal_lit_expr v lit = equal_exprs v (Literal lit)
let equal_undef_expr v = equal_lit_expr v Undefined
let equal_null_expr v = equal_lit_expr v Null
let equal_empty_expr v = equal_lit_expr v Empty
let equal_bool_expr v b = equal_lit_expr v (Bool b)
let equal_loc_expr v l = equal_lit_expr v (LLoc l)
let equal_string_expr v s = equal_lit_expr v (String s)
let equal_int_expr v n = equal_lit_expr v (Num (float_of_int n))
let equal_num_expr v n = equal_lit_expr v (Num n)

let equal_string_exprs e s = equal_exprs e (Literal (String s))

let assign_expr var e = Basic (Assignment (mk_assign var (Expression e)))
let assign_uop var op e = assign_expr var (UnaryOp (op, e))
let assign_to_number var s = assign_uop var ToNumberOp (Literal (String s))
let assign_lit var lit = assign_expr var (Literal lit)
let assign_boolean var b = assign_lit var (Bool b)
let assign_num var n = assign_lit var (Num n)
let assign_string var s = assign_lit var (String s)
let assign_to_string var n = assign_uop var ToStringOp (Literal (Num n))

let assign_true var = assign_boolean var true
let assign_false var = assign_boolean var false

let literal_builtin_field f = Literal (BField f)
let rthis : variable = "rthis"
let rscope : variable = "rscope"

let function_scope_name fid = fid^"_scope"

let add_proto obj proto = 
  Basic (Mutation (mk_mutation (Var obj) (literal_builtin_field FProto) proto))
  
let add_proto_var obj proto =
  add_proto obj (Var proto)
  
let add_proto_value obj proto =
  add_proto obj (Literal (LLoc proto))
  
let add_proto_null obj =
  add_proto obj (Literal Null)

let translate_error_throw error throw_var throw_label meta = (* TODO: Change to use Error.prototype for other errors too *)
  let r1 = mk_assign_fresh Obj in
  mk_stmts meta [
    Basic (Assignment r1); 
    add_proto_value r1.assign_left error; 
    Basic (Mutation (mk_mutation (Var r1.assign_left) (literal_builtin_field FClass) (Literal (String "Error"))));
    Basic (Assignment (mk_assign throw_var (Expression (Var r1.assign_left)))); 
    Goto throw_label
  ]
  
let is_constructor arg meta =
  let hasfield = mk_assign_fresh (HasField (Var arg, literal_builtin_field FConstructId)) in
  mk_stmt meta (Basic (Assignment hasfield)), hasfield.assign_left
  
let translate_inner_call obj vthis args throw_var label_throw env_vars meta =
  (* TODO *)
  let rv = fresh_r () in
  let excep_label = "call_excep." ^ fresh_r () in
  let exit_label = fresh_r () in
  
  let fid = mk_assign_fresh (Lookup (obj, literal_builtin_field FId)) in
  
  let builtincall = mk_assign rv (BuiltinCall (mk_call 
    (Var fid.assign_left) 
    (Literal Empty)  (* No scope for builtin function *)
    vthis 
    args
    excep_label
  )) in
    
  let fscope_eval = mk_assign_fresh Obj in
  let env_stmts = Utils.flat_map (fun env -> 
    [
      Basic (Mutation (mk_mutation (Var fscope_eval.assign_left) (Literal (String env.func_id)) (Var (function_scope_name env.func_id))))
    ]) env_vars in  
  let first_argument = match args with
    | [] -> Literal Undefined
    | arg :: tail -> arg in
  let eval_call = mk_assign rv (Eval (mk_call 
    (Var fid.assign_left) 
    (Var fscope_eval.assign_left) 
    (Var rthis)
    [first_argument]
    excep_label)) in
        
  let fscope = mk_assign_fresh (Lookup (obj, literal_builtin_field FScope)) in
  let call = mk_assign rv (Call (mk_call 
    (Var fid.assign_left) 
    (Var fscope.assign_left) 
    vthis 
    args
    excep_label
  )) in
  
  let mk_stmts = mk_stmts meta in
  mk_stmts [ 
    Basic (Assignment fid);
    Sugar (If (type_of_exp obj (ObjectType (Some Builtin)), mk_stmts [ 
      Sugar (If (equal_loc_expr obj LEval, mk_stmts [ 
        Sugar (If (type_of_exp first_argument StringType, mk_stmts ([ 
          Basic (Assignment fscope_eval);
          add_proto_null fscope_eval.assign_left ] @
          env_stmts @ [ 
          Basic (Assignment eval_call);
          Sugar (If (equal_empty_expr (Var rv), mk_stmts [
            Basic (Assignment (mk_assign rv (Expression (Literal Undefined))))],
            []))
        ]), mk_stmts [
          Basic (Assignment (mk_assign rv (Expression first_argument)))
        ]))
      ], mk_stmts [
        Basic (Assignment builtincall)
      ]));
    ], mk_stmts [ 
      Basic (Assignment fscope); 
      Basic (Assignment call) 
    ]));
    Goto exit_label;
    Label excep_label;
    Basic (Assignment (mk_assign throw_var (Expression (Var rv))));
    Goto label_throw;
    Label exit_label; 
  ], rv

let make_builtin_call id rv vthis args throw_var label_throw meta =
  let vthis = match vthis with
    | None -> Literal Empty
    | Some v -> Var v in
  
  let excep_label = "call_excep." ^ fresh_r () in
  let exit_label = fresh_r () in
  
  let builtincall = mk_assign rv (BuiltinCall (mk_call 
    (Literal (String (string_of_builtin_function id)))
    (Literal Empty)  (* No scope for builtin function *)
    vthis
    args
    excep_label
  )) in
  mk_stmts meta [ 
    Basic (Assignment builtincall);
    Goto exit_label;
    Label excep_label;
    Basic (Assignment (mk_assign throw_var (Expression (Var rv))));
    Goto label_throw;
    Label exit_label;
  ]

let rec to_ivl_goto stmts = 
  List.flatten (List.map (fun stmt ->
      match stmt.stmt_stx with
          | Sugar st -> 
            begin match st with
              | If (c, t1, t2) -> 
                let label1 = fresh_r () in
                let label2 = fresh_r () in
                let label3 = fresh_r () in
                let dt1 = to_ivl_goto t1 in
                let dt2 = to_ivl_goto t2 in
                mk_stmts stmt.stmt_data ([
                  GuardedGoto (c, label1, label2); 
                  Label label1
                ]) @ 
                dt1 @ 
                mk_stmts stmt.stmt_data ([
                  Goto label3; 
                  Label label2
                ]) @ 
                dt2 @ 
                mk_stmts stmt.stmt_data ([
                  Goto label3; 
                  Label label3
                ])
            | _ -> [stmt]
            end
          | _ -> [stmt]
  ) stmts)

let spec_func_get_value arg excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (GetValue arg), excep_label)), left
  
let spec_func_to_object arg excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (ToObject arg), excep_label)), left
  
let spec_func_put_value arg1 arg2 excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (PutValue (arg1, arg2)), excep_label)), left
  
let spec_func_get_own_property arg1 arg2 excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (GetOwnProperty (arg1, arg2)), excep_label)), left
  
let spec_func_get_own_property_default arg1 arg2 excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (GetOwnPropertyDefault (arg1, arg2)), excep_label)), left
  
let spec_func_get_own_property_string arg1 arg2 excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (GetOwnPropertyString (arg1, arg2)), excep_label)), left
  
let spec_func_get arg1 arg2 excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (Get (arg1, arg2)), excep_label)), left
  
let spec_func_get_default arg1 arg2 excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (GetDefault (arg1, arg2)), excep_label)), left
  
let spec_func_get_function arg1 arg2 excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (GetFunction (arg1, arg2)), excep_label)), left
  
let spec_func_put arg1 arg2 arg3 b excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (Put (arg1, arg2, arg3, b)), excep_label)), left
  
let spec_func_has_property arg1 arg2 excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (HasProperty (arg1, arg2)), excep_label)), left
  
let spec_func_delete arg1 arg2 b excep_label =
  let left = fresh_r () in
  Sugar (SpecFunction (left, (Delete (arg1, arg2, b)), excep_label)), left
  
let spec_func_default_value arg1 arg2 excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (DefaultValue (arg1, arg2)), excep_label)), left
  
let spec_func_define_own_property arg1 arg2 arg3 b excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (DefineOwnProperty (arg1, arg2, arg3, b)), excep_label)), left
  
let spec_func_define_own_property_default arg1 arg2 arg3 b excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (DefineOwnPropertyDefault (arg1, arg2, arg3, b)), excep_label)), left
  
let spec_func_define_own_property_array arg1 arg2 arg3 b excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (DefineOwnPropertyArray (arg1, arg2, arg3, b)), excep_label)), left
   
let spec_func_to_primitive arg1 arg2 excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (ToPrimitive (arg1, arg2)), excep_label)), left
  
let spec_func_to_boolean arg excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (ToBoolean arg), excep_label)), left
  
let spec_func_to_number arg excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (ToNumber arg), excep_label)), left
  
let spec_func_to_number_prim arg excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (ToNumberPrim arg), excep_label)), left
  
let spec_func_to_uint32 arg excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (ToUint32 arg), excep_label)), left
  
let spec_func_to_string arg excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (ToString arg), excep_label)), left
  
let spec_func_to_string_prim arg excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (ToStringPrim arg), excep_label)), left
  
let spec_func_check_obj_coer arg excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (CheckObjectCoercible arg), excep_label)), left
  
let spec_func_is_callable arg excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (IsCallable arg), excep_label)), left
  
let spec_func_abstract_relation arg1 arg2 arg3 excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (AbstractRelation (arg1, arg2, arg3)), excep_label)), left
  
let spec_func_strict_equality arg1 arg2 excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (StrictEquality (arg1, arg2)), excep_label)), left
  
let spec_func_strict_equality_same_type arg1 arg2 excep_label = 
  let left = fresh_r () in
  Sugar (SpecFunction (left, (StrictEqualitySameType (arg1, arg2)), excep_label)), left
   
let spec_func_call sp throw_var label_throw meta =
  let excep_label = "spec_call_excep." ^ (fresh_r ()) in (* TODO some of the functions definetely fo not throw exceptions *)
  let exit_label = "spec_call_normal." ^ (fresh_r ()) in
  let sp_stmt, left = 
    match sp with
      | GetValue e -> spec_func_get_value e excep_label
      | PutValue (e1, e2) -> spec_func_put_value e1 e2 excep_label
      | GetOwnProperty (e1, e2) -> spec_func_get_own_property e1 e2 excep_label
      | GetOwnPropertyDefault (e1, e2) -> spec_func_get_own_property_default e1 e2 excep_label
      | GetOwnPropertyString (e1, e2) -> spec_func_get_own_property_string e1 e2 excep_label
      (* At the moment get never throws exceptions, but after implementing getters/setters, it might. *)
      | Get (e1, e2) -> spec_func_get e1 e2 excep_label
      | GetDefault (e1, e2) -> spec_func_get_default e1 e2 excep_label
      | GetFunction (e1, e2) -> spec_func_get_function e1 e2 excep_label
      | Put (e1, e2, e3, b) -> spec_func_put e1 e2 e3 b excep_label
      | HasProperty (e1, e2) -> spec_func_has_property e1 e2 excep_label
      | Delete (e1, e2, b) -> spec_func_delete e1 e2 b excep_label
      | DefaultValue (e, pt) -> spec_func_default_value e pt excep_label (* This not being used at the moment since only to_primitive is using it which is itself a primitive operation *)
      | DefineOwnProperty (e1, e2, e3, b) ->  spec_func_define_own_property e1 e2 e3 b excep_label
      | DefineOwnPropertyDefault (e1, e2, e3, b) -> spec_func_define_own_property_default e1 e2 e3 b excep_label
      | DefineOwnPropertyArray (e1, e2, e3, b) ->  spec_func_define_own_property_array e1 e2 e3 b excep_label
      | ToPrimitive (e, pt) -> spec_func_to_primitive e pt excep_label
      | ToBoolean e -> spec_func_to_boolean e excep_label
      | ToNumber e -> spec_func_to_number e excep_label
      | ToNumberPrim e -> spec_func_to_number_prim e excep_label
      | ToUint32 e -> spec_func_to_uint32 e excep_label
      | ToString e -> spec_func_to_string e excep_label
      | ToStringPrim e -> spec_func_to_string_prim e excep_label
      | ToObject e -> spec_func_to_object e excep_label
      | CheckObjectCoercible e -> spec_func_check_obj_coer e excep_label
      | IsCallable e -> spec_func_is_callable e excep_label
      | AbstractRelation (e1, e2, b) -> spec_func_abstract_relation e1 e2 b excep_label
      | StrictEquality (e1, e2) -> spec_func_strict_equality e1 e2 excep_label
      | StrictEqualitySameType (e1, e2) -> spec_func_strict_equality_same_type e1 e2 excep_label in
    mk_stmts meta [ 
      sp_stmt;
      Goto exit_label;
      Label excep_label;
      Basic (Assignment (mk_assign throw_var (Expression (Var left))));
      Goto label_throw;
      Label exit_label
    ], left
    
let translate_to_object_prim arg left throw_var label_throw meta =
  let bobj = make_builtin_call (Boolean_Construct) left None [arg] throw_var label_throw meta in
  let nobj = make_builtin_call (Number_Construct) left None [arg] throw_var label_throw meta in
  let sobj = make_builtin_call (String_Construct) left None [arg] throw_var label_throw meta in
  mk_stmts meta [ 
    Sugar (If (type_of_exp arg BooleanType,
      bobj, 
      mk_stmts meta [ 
        Sugar (If (type_of_exp arg NumberType,
          nobj,
          sobj))
      ]))
  ]
  
let translate_to_object arg left throw_var label_throw meta =
  mk_stmts meta [
    Sugar (If (or_expr (equal_undef_expr arg) (equal_null_expr arg),
      translate_error_throw Ltep throw_var label_throw meta, mk_stmts meta [ 
      Sugar (If (type_of_exp arg (ObjectType None), mk_stmts meta [
        assign_expr left arg],
        translate_to_object_prim arg left throw_var label_throw meta))
    ]))]
    
let translate_get_default o (* variable containing object *) p (* variable, string, or built-in field name *) left meta = 
   (* TODO : Update everywhere *)
   let desc = mk_assign_fresh (ProtoF (o, p)) in
   mk_stmts meta [
    Basic (Assignment desc);
    Sugar (If (equal_empty_expr (Var desc.assign_left), mk_stmts meta
      [Basic (Assignment (mk_assign left (Expression(Literal Undefined))))], mk_stmts meta
      [Basic (Assignment (mk_assign left (Expression(Var desc.assign_left))))]))
   ] 
  
let translate_get_function o (* variable containing object *) p (* variable, string, or built-in field name *) left throw_var label_throw meta = 
   (* TODO : Update everywhere *)
   let v = fresh_r () in
   let v_stmts= translate_get_default o p v meta in
   v_stmts @
   mk_stmts meta [
    Sugar (If (equal_string_expr p "caller",
      translate_error_throw Ltep throw_var label_throw meta, mk_stmts meta
      [Basic (Assignment (mk_assign left (Expression(Var v))))]))
   ]
  
let translate_get o p left throw_var label_throw meta =
  let classField = mk_assign_fresh (Lookup (o, literal_builtin_field FClass)) in
  let targetField = mk_assign_fresh (HasField (o, literal_builtin_field FTargetFunction)) in
  let get = fresh_r () in
  let getFstmts = translate_get_function o p get throw_var label_throw meta in
  let getstmts = translate_get_default o p get meta in
  let label_default = fresh_r() in
  mk_stmts meta [
    Basic (Assignment classField);
    Sugar (If (equal_string_expr (Var classField.assign_left) "Function", mk_stmts meta
      [ Basic (Assignment targetField);
        Sugar (If (equal_bool_expr (Var targetField.assign_left) false,
         getFstmts, mk_stmts meta
         [Goto label_default]))], mk_stmts meta
      [Label label_default] @
      getstmts));
    Basic (Assignment (mk_assign left (Expression(Var get))))
  ]
    
let translate_gamma_variable_reference_object_lg base field left meta =
  (* This part should follow 10.2.1.2.4 GetBindingValue(N,S). *)
  (* However, when we construct references we make sure we throw required exception then. *)
  (* Hence, simplification here. *)
  (* TODO: double check *)
  let assign_pi_1 = mk_assign left (ProtoF (base, field)) in  
  mk_stmts meta [ Basic (Assignment assign_pi_1) ]
  
let translate_gamma_variable_reference_object_not_lg base field left meta =
  let assign_rv_lookup = mk_assign left (Lookup (base, field)) in   
  mk_stmts meta [Basic (Assignment assign_rv_lookup)]
  
let translate_gamma_variable_reference_object base field left meta =
  mk_stmts meta [ 
    Sugar (If (equal_loc_expr base Lg,
      translate_gamma_variable_reference_object_lg base field left meta,
      translate_gamma_variable_reference_object_not_lg base field left meta)) 
  ]

let translate_gamma_member_reference_object base field left throw_var label_throw meta =
  translate_get base field left throw_var label_throw meta
    
let translate_gamma_reference_prim_base base field left throw_var label_throw meta =
   (* TODO: refactor to it's own function GetForPrim as described in 8.7.1. *)
   let r1 = fresh_r () in 
   let to_object_stmt = translate_to_object base r1 throw_var label_throw in
   let assign_pi = mk_assign_fresh (ProtoF (Var r1, field)) in 
   to_object_stmt meta @
   mk_stmts meta [ 
     Basic (Assignment assign_pi);
     Sugar (If (equal_empty_expr (Var assign_pi.assign_left), mk_stmts meta
       [Basic (Assignment (mk_assign left (Expression(Literal Undefined))))], mk_stmts meta
       [Basic (Assignment (mk_assign left (Expression(Var assign_pi.assign_left))))]))
   ]   
  
let translate_gamma_reference_base_field r base field left throw_var label_throw meta = 
    mk_stmts meta [ 
      Sugar (If (equal_undef_expr base,
        translate_error_throw Lrep throw_var label_throw meta, mk_stmts meta
        [ Sugar (If (istypeof_prim_expr base,
            translate_gamma_reference_prim_base base field left throw_var label_throw meta, mk_stmts meta
            [             
              Sugar (If (type_of_vref r,
                translate_gamma_variable_reference_object base field left meta,
                translate_gamma_member_reference_object base field left throw_var label_throw meta))
            ]))
        ]))
     ]  
     
let translate_gamma_reference r left throw_var label_throw meta = 
  translate_gamma_reference_base_field r (Base r) (Field r) left throw_var label_throw meta
    
  
let translate_gamma r left throw_var label_throw meta =
  let main = Sugar (If (type_of_ref r,
    translate_gamma_reference r left throw_var label_throw meta,
    mk_stmts meta [ Basic (Assignment (mk_assign left (Expression r))) ]))
  in
  mk_stmts meta [main]

let translate_obj_coercible r throw_var label_throw meta =
  mk_stmts meta [ 
    Sugar (If (or_expr (equal_null_expr r) (equal_undef_expr r), 
      translate_error_throw Ltep throw_var label_throw meta, 
      [])) ]
  
  
let translate_call_construct_start f e1 e2s ctx construct meta =
    let r1_stmts, r1 = f e1 in
    let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx.throw_var ctx.label_throw meta in 
    let arg_stmts = List.map (fun e ->
        begin
          let re1_stmts, re1 = f e in
          let re2_stmts, re2 = spec_func_call (GetValue (Var re1)) ctx.throw_var ctx.label_throw meta in 
          (Var re2, re1_stmts @ re2_stmts)
        end
     ) e2s in  
    let arg_values, arg_stmts = List.split arg_stmts in
    let arg_stmts = List.flatten arg_stmts in  
    let gotothrow = translate_error_throw Ltep ctx.throw_var ctx.label_throw meta in
    let is_callable_stmts, is_callable = 
      if construct then begin let stmt, var = is_constructor r2 meta in [stmt], var end
      else spec_func_call (IsCallable (Var r2)) ctx.throw_var ctx.label_throw meta in  
    (
      r1_stmts @ 
      r2_stmts @ 
      arg_stmts @ 
      mk_stmts meta [ Sugar (If (type_of_obj (Var r2), [], gotothrow)) ] @ 
      is_callable_stmts @ 
      mk_stmts meta [ Sugar (If (equal_bool_expr (Var is_callable) false, gotothrow, []))
      ], r1, r2, arg_values)

let translate_get_own_property_default o (* expression containing object *) p (* expression containing property name *) left meta = 
   (* TODO : Update everywhere *)
   let hasfield = mk_assign_fresh (HasField (o, p)) in
   mk_stmts meta [
    Basic (Assignment hasfield);
    Sugar (If (equal_bool_expr (Var hasfield.assign_left) false, mk_stmts meta
      [Basic (Assignment (mk_assign left (Expression(Literal Undefined))))], mk_stmts meta
      [Basic (Assignment (mk_assign left (Lookup (o, p))))]))
   ]     
  
let translate_get_own_property_string o (* expression containing object  *) p (* expression containing property name *) left throw_var label_throw meta = 
   (* TODO : Update everywhere *)
   let desc = fresh_r () in
   let desc_stmt = translate_get_own_property_default o p desc meta in
   desc_stmt @
   mk_stmts meta [
    Sugar (If (equal_undef_expr (Var desc), mk_stmts meta
      [(* TODO Implement Steps 3 - 9 of 15.5.5.2 *)
       Basic (Assignment (mk_assign left (Expression(Literal Undefined))))], mk_stmts meta
      [Basic (Assignment (mk_assign left (Expression(Var desc))))]))
   ]   
  
let translate_get_own_property o p left throw_var label_throw meta =
  let classField = mk_assign_fresh (Lookup (o, literal_builtin_field FClass)) in
  let get_own_property = fresh_r () in
  let get_own_property_string_stmts = translate_get_own_property_string o p get_own_property throw_var label_throw meta in
  let get_own_property_default_stmts = translate_get_own_property_default o p get_own_property meta in
  mk_stmts meta [
    Basic (Assignment classField);
    Sugar (If ((equal_string_expr (Var classField.assign_left) "String"),
      get_own_property_string_stmts,
      get_own_property_default_stmts));
    Basic (Assignment (mk_assign left (Expression(Var get_own_property))))
  ]
  
let is_callable_object arg rv meta = 
  let hasfield = mk_assign_fresh (HasField (arg, literal_builtin_field FId)) in
  mk_stmts meta [  
     Basic (Assignment hasfield);
     Sugar (If (equal_bool_expr (Var hasfield.assign_left) true, mk_stmts meta
       [assign_true rv], mk_stmts meta
       [assign_false rv]))
  ]
  
let is_callable arg rv meta =
  mk_stmts meta [ 
    Sugar (If (type_of_exp arg (ObjectType None),
      is_callable_object arg rv meta, mk_stmts meta
      [assign_false rv]))]
  
let translate_strict_equality_comparison_types_equal_if_equal x y rv meta =
  mk_stmts meta [ Sugar (If (equal_exprs x y, mk_stmts meta [assign_true rv], mk_stmts meta [assign_false rv])) ]
  
let translate_strict_equality_comparison_types_equal_number_not_nan x y rv meta =
  mk_stmts meta [ 
    Sugar (If (or_expr (equal_exprs x y) 
                (or_expr (and_expr (equal_num_expr x 0.0) (equal_num_expr y (-0.0))) 
                         (and_expr (equal_num_expr x (-0.0)) (equal_num_expr y 0.0))), mk_stmts meta
      [assign_true rv], mk_stmts meta
      [assign_false rv]))
  ]
  
let translate_strict_equality_comparison_types_equal_number x y rv meta =
  mk_stmts meta [ 
    Sugar (If (or_expr (equal_num_expr x nan) (equal_num_expr y nan), mk_stmts meta
      [assign_false rv],
      translate_strict_equality_comparison_types_equal_number_not_nan x y rv meta))
  ]
  
let translate_strict_equality_comparison_types_equal x y rv meta =   
    mk_stmts meta [
      Sugar (If (or_expr (type_of_exp x UndefinedType) (type_of_exp x NullType), mk_stmts meta
        [assign_true rv], mk_stmts meta
        [ Sugar (If (or_expr 
                        (type_of_exp x StringType)
                        (or_expr 
                            (type_of_exp x (ObjectType None))
                            (type_of_exp x BooleanType)),
          translate_strict_equality_comparison_types_equal_if_equal x y rv meta, mk_stmts meta
          [ Sugar (If (type_of_exp x NumberType,
              translate_strict_equality_comparison_types_equal_number x y rv meta, mk_stmts meta
              [assign_false rv]))
          ]))
        ]))
    ]
  
let translate_strict_equality_comparison x y rv meta = 
  mk_stmts meta [ 
    Sugar (If (equal_exprs (TypeOf x) (TypeOf y), 
      translate_strict_equality_comparison_types_equal x y rv meta, mk_stmts meta
      [ assign_false rv ]))]
      
let default_value_inner arg m rv exit_label next_label throw_var label_throw meta =
  let r1 = fresh_r () in
  let r1_stmts = translate_get arg (Literal (String m)) r1 throw_var label_throw meta in
  let is_callable_var = fresh_r() in
  let is_callable_stmts = is_callable (Var r1) is_callable_var meta in
  let r2_stmts, r2 = translate_inner_call (Var r1) arg [] throw_var label_throw [] meta in
  let assign_rv_var var = mk_stmts meta [Basic (Assignment (mk_assign rv (Expression (Var var))))] in
  r1_stmts @                          
  is_callable_stmts @ mk_stmts meta [ 
    Sugar (If (equal_bool_expr (Var is_callable_var) true,  
      r2_stmts @ mk_stmts meta
      [ Sugar (If (is_prim_value (Var r2),
        assign_rv_var r2 @ mk_stmts meta 
        [Goto exit_label], mk_stmts meta
        [Goto next_label]))
      ], mk_stmts meta
      [Goto next_label]))
  ]
  
let translate_default_value arg preftype rv throw_var label_throw meta =
  let first, second = 
    (* TODO change to enumeration *)
    (if preftype = (Some StringType) then "toString", "valueOf"
                                     else "valueOf", "toString") in
  let exit_label = fresh_r () in
  let next_label1 = fresh_r () in
  let next_label2 = fresh_r () in
  let r1_stmts = default_value_inner arg first rv exit_label next_label1 throw_var label_throw meta in
  let r2_stmts = default_value_inner arg second rv exit_label next_label2 throw_var label_throw meta in
  r1_stmts @ mk_stmts meta
  [Label next_label1] @
  r2_stmts @ mk_stmts meta
  [Label next_label2] @
  translate_error_throw Ltep throw_var label_throw meta @ mk_stmts meta
  [Label exit_label]
       
let translate_to_primitive arg preftype rv throw_var label_throw meta =
  let r1_stmts = translate_default_value arg preftype rv throw_var label_throw meta in mk_stmts meta
  [
    Sugar (If (type_of_exp arg (ObjectType None),
    r1_stmts, mk_stmts meta
    [assign_expr rv arg]))
  ] 
 
let translate_to_number_bool arg rv meta =
  mk_stmts meta [ 
    Sugar (If (equal_bool_expr arg true, mk_stmts meta
      [assign_num rv 1.0], mk_stmts meta
      [assign_num rv 0.0]))
  ]
  
let translate_to_number_prim arg rv meta =
  mk_stmts meta [
    Sugar (If (type_of_exp arg UndefinedType, mk_stmts meta
      [assign_num rv nan], mk_stmts meta
      [ Sugar (If (type_of_exp arg NullType, mk_stmts meta
        [assign_num rv 0.0], mk_stmts meta
        [ Sugar (If (type_of_exp arg BooleanType,
          translate_to_number_bool arg rv meta, mk_stmts meta
          [ Sugar (If (type_of_exp arg NumberType, mk_stmts meta
            [assign_expr rv arg], mk_stmts meta
            (* Must be StringType *)
            [assign_uop rv ToNumberOp arg]))
          ]))
        ]))
      ]))]
    
let translate_abstract_relation x y leftfirst rv throw_var label_throw meta =
  let px = fresh_r () in
  let to_primitive_x = translate_to_primitive x (Some NumberType) px throw_var label_throw meta in
  let py = fresh_r () in
  let to_primitive_y = translate_to_primitive y (Some NumberType) py throw_var label_throw meta in
  let to_prim_stmts =
    if leftfirst then (to_primitive_x @ to_primitive_y) 
                 else (to_primitive_y @ to_primitive_x) in
  let nx = fresh_r () in
  let to_number_x = translate_to_number_prim (Var px) nx meta in
  let ny = fresh_r () in
  let to_number_y = translate_to_number_prim (Var py) ny meta in
  let assign_rv e = mk_stmts meta [Basic (Assignment (mk_assign rv (Expression e)))] in
  to_prim_stmts @ mk_stmts meta
  [ Sugar (If (and_expr (type_of_exp (Var px) StringType) (type_of_exp (Var py) StringType),
      assign_rv (BinOp (Var px, Comparison LessThan, Var py)), (* TODO: change for new binop prefix? *)
        to_number_x @
        to_number_y @ mk_stmts meta
      [ Sugar (If (or_expr (equal_num_expr (Var nx) nan) (equal_num_expr (Var ny) nan),
          assign_rv (Literal Undefined), mk_stmts meta
          [ Sugar (If (or_expr 
                        (equal_exprs (Var nx) (Var ny))
                        (or_expr 
                          (and_expr (equal_num_expr (Var nx) 0.) (equal_num_expr (Var ny) (-0.))) 
                          (or_expr 
                            (and_expr (equal_num_expr (Var nx) (-0.)) (equal_num_expr (Var ny) 0.)) 
                            (or_expr 
                              (equal_num_expr (Var nx) infinity)
                              (equal_num_expr (Var ny) neg_infinity)))),
              assign_rv (Literal (Bool false)), mk_stmts meta
              [ Sugar (If (or_expr (equal_num_expr (Var nx) neg_infinity) (equal_num_expr (Var ny) infinity),
                  assign_rv (Literal (Bool true)),
                  assign_rv (BinOp (Var nx, Comparison LessThan, Var ny))))
              ]))
          ]))
      ]));
  ]
  
let translate_to_boolean arg rv meta =
  mk_stmts meta [
    Sugar (If (or_expr 
            (equal_undef_expr arg)
            (or_expr 
              (equal_null_expr arg)
              (or_expr 
                (equal_bool_expr arg false)
                (or_expr 
                  (equal_string_expr arg "")
                  (or_expr 
                    (equal_num_expr arg (-0.0))
                    (or_expr 
                      (equal_num_expr arg nan) 
                      (equal_num_expr arg 0.0)))))), mk_stmts meta
      [assign_false rv], mk_stmts meta
      [assign_true rv]))]
    
let translate_to_number_object arg rv throw_var label_throw meta = 
  let primValue = fresh_r () in
  let to_primitive = translate_to_primitive arg (Some NumberType) primValue throw_var label_throw meta in
  let to_number = translate_to_number_prim (Var primValue) rv meta in
     to_primitive @ to_number
    
let translate_to_number arg rv throw_var label_throw meta = 
  let r2 = fresh_r () in
  let primValue = fresh_r () in
  let to_primitive = translate_to_primitive arg (Some NumberType) primValue throw_var label_throw meta in
  let to_number = translate_to_number_prim (Var r2) rv meta in
  mk_stmts meta [ 
    Sugar (If (type_of_exp arg (ObjectType None),
      to_primitive @ mk_stmts meta [assign_expr r2 (Var primValue)], mk_stmts meta
      [assign_expr r2 arg])); 
    ] @ to_number
    
let translate_to_string_bool arg rv meta =
  mk_stmts meta [ 
    Sugar (If (equal_bool_expr arg true, mk_stmts meta
      [assign_string rv "true"], mk_stmts meta
      [assign_string rv "false"]))
  ]
    
let translate_to_string_prim arg rv meta =
  mk_stmts meta [ 
    Sugar (If (type_of_exp arg UndefinedType, mk_stmts meta
      [assign_string rv "undefined"], mk_stmts meta
      [ Sugar (If (type_of_exp arg NullType, mk_stmts meta
        [assign_string rv "null"], mk_stmts meta
        [ Sugar (If (type_of_exp arg BooleanType,
          translate_to_string_bool arg rv meta, mk_stmts meta
          [ Sugar (If (type_of_exp arg StringType, mk_stmts meta
            [assign_expr rv arg],mk_stmts meta
            (* Must be NumberType *)
            [assign_expr rv (UnaryOp (ToStringOp, arg))]))
          ]))
        ]))
      ]))]
      
let translate_to_string_object arg rv throw_var label_throw meta =
  let primValue = fresh_r () in
  let to_primitive = translate_to_primitive arg (Some StringType) primValue throw_var label_throw meta in
  let to_string = translate_to_string_prim (Var primValue) rv meta in
  to_primitive @ to_string
  
      
let translate_to_string arg rv throw_var label_throw meta = 
  let r2 = fresh_r () in
  let primValue = fresh_r () in
  let to_primitive = translate_to_primitive arg (Some StringType) primValue throw_var label_throw meta in
  let to_string = translate_to_string_prim (Var r2) rv meta in
  mk_stmts meta [ 
    Sugar (If (type_of_exp arg (ObjectType None),
      to_primitive @ mk_stmts meta [assign_expr r2 (Var primValue)], mk_stmts meta
      [assign_expr r2 arg]))
    ] @
    to_string
    
let translate_delete o p throw rv throw_var label_throw meta =
  (* TODO update translation to use [[Delete]] *)
  let desc = fresh_r () in
  let desc_stmts = translate_get_own_property o p desc throw_var label_throw meta in
  desc_stmts @ mk_stmts meta
  [ Sugar (If (equal_undef_expr (Var desc), 
      [], mk_stmts meta
      [ Basic (Assignment (mk_assign_fresh (Deallocation (o, p))))]));
    Basic (Assignment (mk_assign_lit rv (Bool true)))  
  ]
      
(* TODO: update when implementing attributes / [[Extensible]] property of an object *)
(* TODO: update translation *)
let translate_define_own_property_default o p desc throw rv throw_var label_throw meta =
  mk_stmts meta
  [ Basic (Mutation (mk_mutation o p desc));
    Basic (Assignment (mk_assign_lit rv (Bool true)))
  ]

let translate_reject throw rv throw_var label_throw meta =
  mk_stmts meta [
      Sugar (If (equal_bool_expr throw true,
        translate_error_throw Ltep throw_var label_throw meta, mk_stmts meta
        [Basic (Assignment (mk_assign_lit rv (Bool false)))]))
  ]
  
(* TODO update translation to use uint32 *)
let translate_to_uint32 input rv throw_var label_throw meta = 
  let number = fresh_r () in
  let number_stmts = translate_to_number input number throw_var label_throw meta in
  (* TODO: More steps from the semantics? *)
  number_stmts @
  mk_stmts meta [Basic (Assignment (mk_assign_e rv (UnaryOp (ToUint32Op, Var number))))]
 
(* TODO update when introducing attributes *)   
let translate_define_own_property_array o p desc throw rv throw_var label_throw meta =
  let oldLen = fresh_r () in
  let oldLen_stmts = translate_get_own_property_default o (Literal (String "length")) oldLen meta in
  let newLen = fresh_r () in
  let newLen_stmts = translate_to_uint32 desc newLen throw_var label_throw meta in
  let newLenToNumber = fresh_r () in
  let newLenToNumber_stmts = translate_to_number desc newLenToNumber throw_var label_throw meta in
  let define_p_length = fresh_r () in
  let define_p_length_stmts = translate_define_own_property_default o (Literal (String "length")) (Var newLen) throw define_p_length throw_var label_throw meta in
  let newLen_less_than_oldLen = mk_assign_fresh_e (BinOp (Var newLen, Comparison LessThan, Var oldLen)) in
  let succeeded_j = fresh_r () in
  let define_length_j_stmts = translate_define_own_property_default o (Literal (String "length")) (Var newLen) throw succeeded_j throw_var label_throw meta in
  let loop_head_label = "loop_head." ^ fresh_r () in
  let loop_exit_label = "loop_exit." ^ fresh_r () in
  let oldLen2 = fresh_r () in
  let to_string_old_len = fresh_r () in
  let to_string_old_len_stmts = translate_to_string_prim (Var oldLen2) to_string_old_len meta in
  let newLen_less_than_oldLen_l = mk_assign_fresh_e (BinOp (Var newLen, Comparison LessThan, Var oldLen)) in
  let delete_stmts = translate_delete o (Var to_string_old_len) false (fresh_r()) throw_var label_throw meta in
  let index = fresh_r () in
  let touint32_stmts = translate_to_uint32 p index throw_var label_throw meta in
  let tostring = fresh_r () in
  let tostring_stmts = translate_to_string_prim (Var index) tostring meta in
  let succeeded = fresh_r () in
  let define_index_prop_stmts = translate_define_own_property_default o p desc false succeeded throw_var label_throw meta in
  let index_less_than_length = mk_assign_fresh_e (BinOp (Var index, Comparison LessThan, Var oldLen)) in
  let define_len = fresh_r () in
  let define_len_stmts = translate_define_own_property_default o (Literal (String "length")) (BinOp (Var index, Arith Plus, Literal (Num 1.0))) false define_len throw_var label_throw meta in
  let define_prop_r = fresh_r () in
  let define_prop_stmts = translate_define_own_property_default o p desc throw define_prop_r throw_var label_throw meta in
  oldLen_stmts @
  mk_stmts meta
  [ Sugar (If (equal_string_expr p "length", 
      newLen_stmts @
      newLenToNumber_stmts @ mk_stmts meta
      [ Sugar (If (equal_exprs (Var newLen) (Var newLenToNumber), mk_stmts meta
        [ Basic (Assignment newLen_less_than_oldLen);
          Sugar (If (equal_bool_expr (Var newLen_less_than_oldLen.assign_left) false, (* newLen >= oldLen *)
            define_p_length_stmts @ mk_stmts meta
            [ Basic (Assignment (mk_assign_e rv (Var define_p_length))) ], 
              define_length_j_stmts @ mk_stmts meta
              [ Sugar (If (equal_bool_expr (Var succeeded_j) false,  mk_stmts meta
                  [ Basic (Assignment (mk_assign_lit rv (Bool false))) ], mk_stmts meta
                  (* Simplification for now since delete always returns true. Update when introducing attributes *)
                  [ Label loop_head_label;
                    Basic (Assignment (newLen_less_than_oldLen_l));
                    Sugar (If (equal_bool_expr (Var newLen_less_than_oldLen_l.assign_left) true, mk_stmts meta
                      [ Basic (Assignment (mk_assign_e oldLen2 (BinOp (Var oldLen, Arith Minus, Literal (Num 1.0))))) ] @ (* Not SSA *) 
                        to_string_old_len_stmts @ 
                        delete_stmts @ mk_stmts meta
                        [Basic (Assignment (mk_assign_e oldLen (Var oldLen2)))]  @ mk_stmts meta
                      [ Goto loop_head_label ], mk_stmts meta
                      [ Goto loop_exit_label ]));
                    Label loop_exit_label;
                    Basic (Assignment (mk_assign_lit rv (Bool true)))                     
                  ])) 
              ]))],
        translate_error_throw LRangeErrorP throw_var label_throw meta))],
      touint32_stmts @
      tostring_stmts @ mk_stmts meta [  
        Sugar (If (equal_exprs (Var tostring) p, 
          (* Index *)
          define_index_prop_stmts @ mk_stmts meta
          [ Sugar (If (equal_bool_expr (Var succeeded) false, 
            translate_reject (Literal (Bool throw)) rv throw_var label_throw meta, mk_stmts meta
            [ Basic (Assignment index_less_than_length);
              Sugar (If (equal_bool_expr (Var index_less_than_length.assign_left) false, 
                define_len_stmts @ mk_stmts meta
                [Basic (Assignment (mk_assign_e rv (Var define_len)))], mk_stmts meta
                [Basic (Assignment (mk_assign_lit rv (Bool true)))]))
            ]))],
          (* Other property *)
          define_prop_stmts @ mk_stmts meta
          [Basic (Assignment (mk_assign_e rv (Var define_prop_r)))]))
      ]))
  ]
  
let translate_define_own_property o p desc throw rv throw_var label_throw meta =
  let classField = mk_assign_fresh (Lookup (o, literal_builtin_field FClass)) in
  let def = fresh_r () in
  let def_stmts_default = translate_define_own_property_default o p desc throw def throw_var label_throw meta in
  let def_stmts_array = translate_define_own_property_array o p desc throw def throw_var label_throw meta in
  mk_stmts meta [
    Basic (Assignment classField);
    Sugar (If (equal_string_expr (Var classField.assign_left) "Array",
      def_stmts_array,
      def_stmts_default));
    Basic (Assignment (mk_assign_e rv (Var def)))
  ]
      
(* TODO: update when implementing setters/getters and attributes *)
(* TODO: update translation *)   
let translate_put o p v throw throw_var label_throw meta = 
  translate_define_own_property o p v throw (fresh_r()) throw_var label_throw meta 
      
let translate_put_value_member_reference_object_base_field base field value throw_var throw_label meta =
  translate_put base field value true throw_var throw_label meta
  
let translate_put_value_member_reference_object ref value throw_var throw_label meta =
  translate_put_value_member_reference_object_base_field (Base ref) (Field ref) value throw_var throw_label meta
  
let translate_put_value_variable_reference_object v1 v2 throw_var throw_label meta =
  mk_stmts meta [   
    Sugar (If (equal_loc_expr (Base v1) Lg,
      translate_put_value_member_reference_object v1 v2 throw_var throw_label meta, mk_stmts meta
      [Basic (Mutation (mk_mutation (Base v1) (Field v1) v2))])) 
  ]
  
let translate_put_value_reference_base v1 base v2 throw_var throw_label meta =
  let gotothrow = translate_error_throw Lrep throw_var throw_label meta in
  mk_stmts meta [ 
    Sugar (If (equal_undef_expr base, 
      gotothrow, mk_stmts meta
      [
        Sugar (If (istypeof_prim_expr base, 
          (* TODO: follow the spec by creating special [[Put]] as defined in 8.7.2 *)
          gotothrow, mk_stmts meta
          [ Sugar (If (type_of_vref v1,
              translate_put_value_variable_reference_object v1 v2 throw_var throw_label meta,
              translate_put_value_member_reference_object v1 v2 throw_var throw_label meta)) ]))
      ]))
    ]
    
let translate_put_value_reference v1 v2 throw_var throw_label meta =
  translate_put_value_reference_base v1 (Base v1) v2 throw_var throw_label meta
  
let translate_put_value v1 v2 throw_var throw_label meta =
  mk_stmts meta [ 
    Sugar (If (type_of_ref v1,
      translate_put_value_reference v1 v2 throw_var throw_label meta,
      translate_error_throw Lrep throw_var throw_label meta))
  ]
    
let translate_has_property o p rv meta =
  (* TODO use this in other places too *) 
  let assign_pi = mk_assign_fresh (ProtoF (o, p)) in 
    mk_stmts meta [ 
      Basic (Assignment assign_pi);
      Sugar (If (equal_empty_expr (Var assign_pi.assign_left), mk_stmts meta
        [assign_false rv], mk_stmts meta
        [assign_true rv])) 
    ]
    
let translate_new_array rv meta =
  let new_obj = mk_assign rv Obj in
  mk_stmts meta [ Basic (Assignment new_obj);
    add_proto_value new_obj.assign_left Lap;
    (* TODO refactor add_class *)
    Basic (Mutation (mk_mutation (Var new_obj.assign_left) (literal_builtin_field FClass) (Literal (String "Array"))));
    Basic (Mutation (mk_mutation (Var new_obj.assign_left) (Literal (String "length")) (Literal (Num 0.0))));
  ]
    
let unfold_spec_function sf left throw_var label_throw meta =
  match sf with
    | GetValue e -> translate_gamma e left throw_var label_throw meta
    | PutValue (e1, e2) -> translate_put_value e1 e2 throw_var label_throw meta
    | GetOwnProperty (e1, e2) -> translate_get_own_property e1 e2 left throw_var label_throw meta
    | GetOwnPropertyDefault (e1, e2) -> translate_get_own_property_default e1 e2 left meta
    | GetOwnPropertyString (e1, e2) -> translate_get_own_property_string e1 e2 left throw_var label_throw meta
    | GetDefault (e1, e2) -> translate_get_default e1 e2 left meta
    | GetFunction (e1, e2) -> translate_get_function e1 e2 left throw_var label_throw meta
    | Get (e1, e2) -> translate_get e1 e2 left throw_var label_throw meta
    | Put (e1, e2, e3, b) -> translate_put e1 e2 e3 b throw_var label_throw meta
    | HasProperty (e1, e2) -> translate_has_property e1 e2 left meta
    | Delete (e1, e2, b) -> translate_delete e1 e2 b left throw_var label_throw meta
    | DefaultValue (e, pt) -> translate_default_value e pt left throw_var label_throw meta
    | DefineOwnProperty (e1, e2, e3, b) -> translate_define_own_property e1 e2 e3 b left throw_var label_throw meta
    | DefineOwnPropertyDefault (e1, e2, e3, b) ->  translate_define_own_property_default e1 e2 e3 b left throw_var label_throw meta
    | DefineOwnPropertyArray (e1, e2, e3, b) ->  translate_define_own_property_array e1 e2 e3 b left throw_var label_throw meta
    | ToPrimitive (e, pt) -> translate_to_primitive e pt left throw_var label_throw meta
    | ToBoolean e -> translate_to_boolean e left meta
    | ToNumber e -> translate_to_number e left throw_var label_throw meta
    | ToNumberPrim e -> translate_to_number_prim e left meta
    | ToUint32 e -> translate_to_uint32 e left throw_var label_throw meta
    | ToString e -> translate_to_string e left throw_var label_throw meta
    | ToStringPrim e -> translate_to_string_prim e left meta
    | ToObject e -> translate_to_object e left throw_var label_throw meta
    | CheckObjectCoercible e -> translate_obj_coercible e throw_var label_throw meta
    | IsCallable e -> is_callable e left meta
    | AbstractRelation (e1, e2, b) -> translate_abstract_relation e1 e2 b left throw_var label_throw meta
    | StrictEquality (e1, e2) -> translate_strict_equality_comparison e1 e2 left meta
    | StrictEqualitySameType (e1, e2) -> translate_strict_equality_comparison_types_equal e1 e2 left meta

let unfold_spec_function_leave_gamma sf left throw_var label_throw meta =
  match sf with
    | GetValue e -> mk_stmts meta [Sugar (SpecFunction (left, sf, label_throw))]
    | _ -> unfold_spec_function sf left throw_var label_throw meta

let rec unfold_spec_functions unfold_f stmts = 
  let f = unfold_spec_functions unfold_f in
    List.flatten (List.map (fun stmt ->
      match stmt.stmt_stx with
          | Sugar st -> 
            begin match st with
              | If (c, t1, t2) -> [{stmt with stmt_stx = Sugar (If (c, f t1, f t2))}]
              | SpecFunction (left, sf, excep_label) -> 
                unfold_f sf left left excep_label stmt.stmt_data
            end
          | _ -> [stmt]
  ) stmts)
  
let to_ivl_goto_unfold stmts = to_ivl_goto (unfold_spec_functions unfold_spec_function stmts)
let to_ivl_goto_unfold_leave_gamma stmts = to_ivl_goto (unfold_spec_functions unfold_spec_function_leave_gamma stmts)