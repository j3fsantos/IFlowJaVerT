open Batteries
open Pulp_Syntax
open Pulp_Syntax_Utils
open Pulp_Syntax_Print
open Pulp_Procedure

exception PulpNotImplemented of string
exception PulpInvalid of string

type translation_level =
  | IVL_buitin_functions
  | IVL_conditionals
  | IVL_goto

type switch_record = { (* Special constants for throws and returns *)
    a_cases : (Parser_syntax.exp * Parser_syntax.exp) list; 
		b_cases : (Parser_syntax.exp * Parser_syntax.exp) list; 
		default : Parser_syntax.exp option
}	
  
let rthis : variable = "rthis"
let rscope : variable = "rscope"

let function_scope_name fid =
  fid^"_scope"
  
let end_label : label = "theend"

let literal_builtin_field f = Literal (String (string_of_builtin_field f))

let is_ref_inner ref rt =
  IsTypeOf (Var ref, ReferenceType rt)
  
let is_oref_expr ref = is_ref_inner ref (Some MemberReference)
let is_vref_expr ref = is_ref_inner ref (Some VariableReference)
let is_ref_expr ref = is_ref_inner ref None

let or_expr e1 e2 = BinOp (e1, Boolean Or, e2)
let and_expr e1 e2 = BinOp (e1, Boolean And, e2)
let not_expr e1 = UnaryOp (Not, e1)
let equal_exprs e1 e2 = BinOp (e1, Comparison Equal, e2)
let equal_expr v e2 = equal_exprs (Var v) e2

let lessthan_exprs e1 e2 = or_expr 
    (BinOp (e1, Comparison LessThan, e2)) 
    (BinOp (e1, Comparison Equal, e2))
    
let concat_exprs e1 e2 = BinOp (e1, Concat, e2)
 
let type_of_var v t = 
  let typeof = TypeOf (Var v) in
  let typelit = Literal (Type t) in
  match t with
    | NullType
    | UndefinedType
    | NumberType
    | StringType
    | BooleanType ->  BinOp (typeof, Comparison Equal, typelit)
    | ObjectType _
    | ReferenceType _ -> lessthan_exprs typeof typelit
    
let type_of_oref_var ref = type_of_var ref (ReferenceType (Some MemberReference))
let type_of_vref_var ref = type_of_var ref (ReferenceType (Some VariableReference))
let type_of_ref_var ref = type_of_var ref (ReferenceType None)

let type_of_obj obj = type_of_var obj (ObjectType None)
  
let istypeof_prim_expr v =
  or_expr 
  (type_of_var v BooleanType)
  (or_expr 
     (type_of_var v NumberType)
     (type_of_var v StringType))
    
let is_prim_value v =
  or_expr 
  (type_of_var v UndefinedType)
  (or_expr 
    (type_of_var v NullType)
    (istypeof_prim_expr v)
  )  
    
		
let equal_lit_expr v lit = equal_expr v (Literal lit)
let equal_undef_expr v = equal_lit_expr v Undefined
let equal_null_expr v = equal_lit_expr v Null
let equal_empty_expr v = equal_lit_expr v Empty
let equal_bool_expr v b = equal_lit_expr v (Bool b)
let equal_loc_expr v l = equal_lit_expr v (LLoc l)
let equal_string_expr v s = equal_lit_expr v (String s)
let equal_int_expr v n = equal_lit_expr v (Num (float_of_int n))
let equal_num_expr v n = equal_lit_expr v (Num n)

let equal_string_exprs e s = equal_exprs e (Literal (String s))

(* TODO Change NotImplemented --> CannotHappen *)
let tr_unary_op op =
  match op with
      | Parser_syntax.Not -> Not
      | Parser_syntax.TypeOf -> raise (PulpNotImplemented ((Pretty_print.string_of_unary_op op ^ " REF:11.4.3 The typeof Operator.")))
      | Parser_syntax.Positive -> raise (PulpNotImplemented ((Pretty_print.string_of_unary_op op ^ " REF:11.4.6 Unary + Operator.")))
      | Parser_syntax.Negative -> raise (PulpNotImplemented ((Pretty_print.string_of_unary_op op ^ " REF:11.4.7 Unary - Operator.")))
      | Parser_syntax.Pre_Decr -> raise (PulpNotImplemented ((Pretty_print.string_of_unary_op op ^ " REF:11.4.5 Prefix Decrement Operator.")))
      | Parser_syntax.Post_Decr -> raise (PulpNotImplemented ((Pretty_print.string_of_unary_op op ^ " REF:11.3.2 Postfix Decrement Operator.")))
      | Parser_syntax.Pre_Incr -> raise (PulpNotImplemented ((Pretty_print.string_of_unary_op op ^ " REF:11.4.4 Prefix Increment Operator.")))
      | Parser_syntax.Post_Incr -> raise (PulpNotImplemented ((Pretty_print.string_of_unary_op op ^ " REF:11.3.1 Postfix Increment Operator.")))
      | Parser_syntax.Bitnot -> raise (PulpNotImplemented ((Pretty_print.string_of_unary_op op ^ " REF:11.4.8 Bitwise NOT Operator.")))
      | Parser_syntax.Void -> raise (PulpNotImplemented ((Pretty_print.string_of_unary_op op ^ " REF:11.4.2 The void Operator.")))

let tr_arith_op op =
  begin match op with
      | Parser_syntax.Plus -> Arith Plus
      | Parser_syntax.Minus -> Arith Minus
      | Parser_syntax.Times -> Arith Times
      | Parser_syntax.Div -> Arith Div
      | Parser_syntax.Mod -> Arith Mod
      | Parser_syntax.Ursh -> Bitwise UnsignedRightShift
      | Parser_syntax.Lsh -> Bitwise LeftShift
      | Parser_syntax.Rsh -> Bitwise SignedRightShift
      | Parser_syntax.Bitand -> Bitwise BitwiseAnd
      | Parser_syntax.Bitor -> Bitwise BitwiseOr
      | Parser_syntax.Bitxor -> Bitwise BitwiseXor
  end
  
let tr_comparison_op op =
  begin match op with
    | Parser_syntax.Equal -> Equal
    | Parser_syntax.NotEqual -> raise (PulpNotImplemented ((Pretty_print.string_of_comparison_op op ^ " REF:11.9.2 The Does-not-equals Operator.")))
    | Parser_syntax.TripleEqual -> raise (PulpNotImplemented ((Pretty_print.string_of_comparison_op op ^ " REF:11.9.4 The Strict Equals Operator.")))
    | Parser_syntax.NotTripleEqual -> raise (PulpNotImplemented ((Pretty_print.string_of_comparison_op op ^ " REF:11.9.5 The Strict Does-not-equal Operator.")))
    | Parser_syntax.Lt -> LessThan
    | Parser_syntax.Le -> LessThan
    | Parser_syntax.Gt -> LessThan
    | Parser_syntax.Ge -> LessThan
    | Parser_syntax.In -> raise (PulpNotImplemented ((Pretty_print.string_of_comparison_op op ^ " REF:11.8.7 The in operator.")))
    | Parser_syntax.InstanceOf -> raise (PulpNotImplemented ((Pretty_print.string_of_comparison_op op ^ " REF:11.8.6 The instanceof operator.")))
  end
  
let tr_boolean_op op =
  begin match op with
    | Parser_syntax.And -> And
    | Parser_syntax.Or -> Or
  end

let tr_bin_op op =
  match op with
    | Parser_syntax.Comparison op -> Comparison (tr_comparison_op op)
    | Parser_syntax.Arith op -> tr_arith_op op
    | Parser_syntax.Boolean op -> Boolean (tr_boolean_op op)

let tr_propname pn : string =
  match pn with
  | Parser_syntax.PropnameId s -> s
  | Parser_syntax.PropnameString s -> s
  | Parser_syntax.PropnameNum f -> string_of_float f
  
let add_proto obj proto = 
  Basic (Mutation (mk_mutation (Var obj) (literal_builtin_field FProto) proto))
  
let add_proto_var obj proto =
  add_proto obj (Var proto)
  
let add_proto_value obj proto =
  add_proto obj (Literal (LLoc proto))
  
let add_proto_null obj =
  add_proto obj (Literal Null)
  
let is_callable arg =
  let rv =  fresh_r () in
  let rv_true = Basic (Assignment (mk_assign rv (Expression (Literal (Bool true))))) in
  let rv_false = Basic (Assignment (mk_assign rv (Expression (Literal (Bool false))))) in
  let hasfield = mk_assign_fresh (HasField (Var arg, literal_builtin_field FId)) in
  Sugar (If (type_of_var arg (ObjectType None),
    [Basic (Assignment hasfield);
     Sugar (If (equal_bool_expr hasfield.assign_left true,
       [rv_true],
       [rv_false]))
    ],
    [rv_false])), rv
    
let is_constructor arg =
  let hasfield = mk_assign_fresh (HasField (Var arg, literal_builtin_field FConstructId)) in
  Basic (Assignment hasfield), hasfield.assign_left
  
let translate_strict_equality_comparison_types_equal x y rv = 
  let rv_true = Basic (Assignment (mk_assign rv (Expression (Literal (Bool true))))) in
  let rv_false = Basic (Assignment (mk_assign rv (Expression (Literal (Bool false))))) in
  
  (* TODO Change this to less branch *) 
    [
      Sugar (If (or_expr (IsTypeOf (Var x, UndefinedType)) (IsTypeOf (Var x, NullType)),
        [rv_true], 
        [
          Sugar (If (or_expr 
                        (IsTypeOf (Var x, StringType))
                        (or_expr 
                            (IsTypeOf (Var x, (ObjectType None)))
                            (IsTypeOf (Var x, BooleanType))),
          [
            Sugar (If (equal_expr x (Var y), [rv_true], [rv_false]))
          ],
          [
            Sugar (If (IsTypeOf (Var x, NumberType),
            [
              Sugar (If (equal_num_expr x nan, 
              [rv_false],
              [
                Sugar (If (equal_num_expr y nan, 
                [rv_false],
                [
                  Sugar (If (equal_expr x (Var y), 
                  [rv_true], 
                  [
                    Sugar (If (and_expr (equal_num_expr x 0.0) (equal_num_expr y (-0.0)),
                    [rv_true],
                    [
                      Sugar (If (and_expr (equal_num_expr x (-0.0)) (equal_num_expr y 0.0),
	                    [rv_true],
	                    [rv_false]))
                    ]))
                  ]))
                ]))
              ]))
            ],
            [rv_false]))
          ]
          ))
        ]))
    ]
  
let translate_strict_equality_comparison x y = 
  let rv = fresh_r() in
  let stmts = translate_strict_equality_comparison_types_equal x y rv in
  Sugar (If (equal_exprs (TypeOf (Var x)) (TypeOf (Var y)), 
    stmts,
    [ Basic (Assignment (mk_assign rv (Expression (Literal (Bool false))))) ])), rv
  
let translate_error_throw error throw_var throw_label = (* TODO: Change to use Error.prototype for other errors too *)
  let r1 = mk_assign_fresh Obj in
  [
    Basic (Assignment r1); 
    add_proto_value r1.assign_left error; 
    Basic (Mutation (mk_mutation (Var r1.assign_left) (literal_builtin_field FClass) (Literal (String "Error"))));
    Basic (Assignment (mk_assign throw_var (Expression (Var r1.assign_left)))); 
    Goto throw_label
  ]
  
let translate_put_value v1 v2 throw_var throw_label =
  let gotothrow = translate_error_throw Lrep throw_var throw_label in
  let base = mk_assign_fresh_e (Base (Var v1)) in
  let hasField = mk_assign_fresh (HasField (Var base.assign_left, Field (Var v1))) in
  let main = Sugar (If (is_ref_expr v1,
    [
      Basic (Assignment base);
      Sugar (If (equal_undef_expr base.assign_left, 
        gotothrow, 
        [
          Sugar (If (istypeof_prim_expr base.assign_left, 
            translate_error_throw Ltep throw_var throw_label, 
            [ Sugar (If (and_expr (is_vref_expr v1) (equal_loc_expr base.assign_left Lg), 
              [Basic (Assignment (hasField));
               Sugar (If (equal_bool_expr hasField.assign_left true,
                 [Basic (Mutation (mk_mutation (Var base.assign_left) (Field (Var v1)) (Var v2)))],
                  gotothrow))
              ],
              [Basic (Mutation (mk_mutation (Var base.assign_left) (Field (Var v1)) (Var v2)))]))
            ]))
        ]))
    ],
    gotothrow))
  in
  main
  
let make_builtin_call id rv vthis args ctx =
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
  [ Basic (Assignment builtincall);
    Goto exit_label;
    Label excep_label;
    Basic (Assignment (mk_assign ctx.throw_var (Expression (Var rv))));
    Goto ctx.label_throw;
    Label exit_label;
  ]
  
let translate_to_object arg ctx =
  let rv = fresh_r () in
  let assign_rv_var var = [Basic (Assignment (mk_assign rv (Expression (Var var))))] in
  let bobj = make_builtin_call (Boolean_Construct) rv None [Var arg] ctx in
  let nobj = make_builtin_call (Number_Construct) rv None [Var arg] ctx in
  let sobj = make_builtin_call (String_Construct) rv None [Var arg] ctx in
  Sugar (If (or_expr (equal_undef_expr arg) (equal_null_expr arg),
    translate_error_throw Ltep ctx.throw_var ctx.label_throw,
    [ Sugar (If (type_of_var arg (ObjectType None),
      assign_rv_var arg,
      [ Sugar (If (type_of_var arg BooleanType,
        bobj,
        [ Sugar (If (type_of_var arg NumberType,
            nobj,
            sobj))
        ]))
      ]))
    ])), rv
  
let translate_gamma r ctx =
  let rv = fresh_r () in
  let base = mk_assign_fresh_e (Base (Var r)) in
  let field = mk_assign_fresh_e (Field (Var r)) in
  let assign_rv_lookup = mk_assign rv (Lookup (Var base.assign_left, Var field.assign_left)) in
  let assign_pi_1 = mk_assign_fresh (ProtoF (Var base.assign_left, Var field.assign_left)) in  
  let assign_pi_2 = mk_assign_fresh (ProtoF (Var base.assign_left, Var field.assign_left)) in  
  let to_object_stmt, r1 = translate_to_object base.assign_left ctx in
  let assign_pi = mk_assign_fresh (ProtoF (Var r1, Var field.assign_left)) in 
  let main = Sugar (If (is_ref_expr r,
    [
      Basic (Assignment base);
      Sugar (If (equal_undef_expr base.assign_left,
        translate_error_throw Lrep ctx.throw_var ctx.label_throw,
        [ Basic (Assignment field);
          Sugar (If (istypeof_prim_expr base.assign_left,
            [ to_object_stmt;
              Basic (Assignment assign_pi);
              Sugar (If (equal_empty_expr assign_pi.assign_left,
                [Basic (Assignment (mk_assign rv (Expression(Literal Undefined))))],
                [Basic (Assignment (mk_assign rv (Expression(Var assign_pi.assign_left))))]))
            ],
            [             
              Sugar (If (is_vref_expr r,
                [ 
                  Sugar (If (equal_loc_expr base.assign_left Lg,
                  [
                    Basic (Assignment assign_pi_1);
                    Sugar (If (equal_empty_expr assign_pi_1.assign_left,
                      translate_error_throw Lrep ctx.throw_var ctx.label_throw,
                      [Basic (Assignment (mk_assign rv (Expression(Var assign_pi_1.assign_left))))]))
                  ],
                  [Basic (Assignment assign_rv_lookup)])) 
                ],
                [ Basic (Assignment assign_pi_2);
                  Sugar (If (equal_empty_expr assign_pi_2.assign_left,
                    [Basic (Assignment (mk_assign rv (Expression(Literal Undefined))))],
                    [Basic (Assignment (mk_assign rv (Expression(Var assign_pi_2.assign_left))))])) 
                ]))
            ]))
        ]))
    ],
    [ Basic (Assignment (mk_assign rv (Expression (Var r)))) ]))
  in
  [main], rv

let translate_obj_coercible r ctx =
  let rv = fresh_r () in
  let gotothrow = translate_error_throw Ltep ctx.throw_var ctx.label_throw in 
  [
    Sugar (If (equal_null_expr r, gotothrow, [])); 
    Sugar (If (equal_undef_expr r, gotothrow, [])); 
    Basic (Assignment (mk_assign rv (Expression (Literal Empty))))
  ], rv
  
let translate_call_construct_start f e1 e2s ctx construct =
    let r1_stmts, r1 = f e1 in
    let r2_stmts, r2 = translate_gamma r1 ctx in 
    let arg_stmts = List.map (fun e ->
        begin
          let re1_stmts, re1 = f e in
          let re2_stmts, re2 = translate_gamma re1 ctx in 
          (Var re2, re1_stmts @ re2_stmts)
        end
     ) e2s in  
    let arg_values, arg_stmts = List.split arg_stmts in
    let arg_stmts = List.flatten arg_stmts in  
    let gotothrow = translate_error_throw Ltep ctx.throw_var ctx.label_throw in
    let is_callable_stmt, is_callable = 
      if construct then is_constructor r2
      else is_callable r2 in  
    (
      r1_stmts @ 
      r2_stmts @ 
      arg_stmts @ 
      [
        Sugar (If (type_of_obj r2, [], gotothrow)); 
        is_callable_stmt; 
        Sugar (If (equal_bool_expr is_callable false, gotothrow, []))
      ], r1, r2, arg_values)
      
let translate_get o (* variable containing object *) p (* variable, string, or built-in field name *) = 
   (* TODO : Update everywhere *)
   let rv = fresh_r () in
   let desc = mk_assign_fresh (ProtoF (Var o, p)) in
   [Basic (Assignment desc);
    Sugar (If (equal_empty_expr desc.assign_left,
      [Basic (Assignment (mk_assign rv (Expression(Literal Undefined))))],
      [Basic (Assignment (mk_assign rv (Expression(Var desc.assign_left))))]))
   ], rv 
  
let translate_inner_call obj vthis args ctx =
  (* TODO *)
  let rv = fresh_r () in
  let excep_label = "call_excep." ^ fresh_r () in
  let exit_label = fresh_r () in
  
  let fid = mk_assign_fresh (Lookup (Var obj, literal_builtin_field FId)) in
  
  let builtincall = mk_assign rv (BuiltinCall (mk_call 
    (Var fid.assign_left) 
    (Literal Empty)  (* No scope for builtin function *)
    (Var vthis) 
    args
    excep_label
  )) in
    
  let fscope_eval = mk_assign_fresh Obj in
  let env_stmts = Utils.flat_map (fun env -> 
    [
      Basic (Mutation (mk_mutation (Var fscope_eval.assign_left) (Literal (String env.func_id)) (Var (function_scope_name env.func_id))))
    ]) ctx.env_vars in  
  let first_argument = match args with
    | [] -> Literal Undefined
    | arg :: tail -> arg in
  let eval_call = mk_assign rv (Eval (mk_call 
    (Var fid.assign_left) 
    (Var fscope_eval.assign_left) 
    (Var vthis) 
    [first_argument]
    excep_label)) in
        
  let fscope = mk_assign_fresh (Lookup (Var obj, literal_builtin_field FScope)) in
  let call = mk_assign rv (Call (mk_call 
    (Var fid.assign_left) 
    (Var fscope.assign_left) 
    (Var vthis) 
    args
    excep_label
  )) in
  
  [ Basic (Assignment fid);
    Sugar (If (type_of_var obj (ObjectType (Some Builtin)),
    [ Sugar (If (equal_loc_expr obj LEval,
      [ Sugar (If ((*equal_exprs (TypeOf first_argument) (Literal (Type StringType))*) IsTypeOf (first_argument, StringType),
        [ Basic (Assignment fscope_eval);
          add_proto_null fscope_eval.assign_left
        ] @
        env_stmts @
        [Basic (Assignment eval_call);
         Sugar (If (equal_empty_expr rv,
           [Basic (Assignment (mk_assign rv (Expression (Literal Undefined))))],
           []))
        ],       
        [Basic (Assignment (mk_assign rv (Expression first_argument)))]))
      ], 
      [Basic (Assignment builtincall)]));
    ],
    [ Basic (Assignment fscope); 
      Basic (Assignment call) 
    ]));
    Goto exit_label;
    Label excep_label;
    Basic (Assignment (mk_assign ctx.throw_var (Expression (Var rv))));
    Goto ctx.label_throw;
    Label exit_label; 
  ], rv
      
let default_value_inner arg m rv exit_label next_label ctx =
  let r1_stmts, r1 = translate_get arg (Literal (String m)) in
  let is_callable_stmt, is_callable = is_callable r1 in
  let r2_stmts, r2 = translate_inner_call r1 arg [] ctx in
  let assign_rv_var var = [Basic (Assignment (mk_assign rv (Expression (Var var))))] in
  r1_stmts @                          
  [ is_callable_stmt;
    Sugar (If (equal_bool_expr is_callable true,  
      r2_stmts @
    [ Sugar (If (is_prim_value r2,
      assign_rv_var r2 @ [Goto exit_label],
      [Goto next_label]))
    ],
    [Goto next_label]))
  ]
  
let translate_default_value arg preftype ctx =
  let first, second = 
    (* TODO change to enumeration *)
    (if preftype = (Some StringType) then "toString", "valueOf"
                                     else "valueOf", "toString") in
  let rv = fresh_r () in
  let exit_label = fresh_r () in
  let next_label1 = fresh_r () in
  let next_label2 = fresh_r () in
  let r1_stmts = default_value_inner arg first rv exit_label next_label1 ctx in
  let r2_stmts = default_value_inner arg second rv exit_label next_label2 ctx in
  r1_stmts @
  [Label next_label1] @
  r2_stmts @
  [Label next_label2] @
  translate_error_throw Ltep ctx.throw_var ctx.label_throw @
  [Label exit_label], rv 
      
let translate_to_primitive arg preftype ctx =
  let rv = fresh_r () in
  let assign_rv_var var = [Basic (Assignment (mk_assign rv (Expression (Var var))))] in
  let r1_stmts, r1 = translate_default_value arg preftype ctx in
  [
    Sugar (If (type_of_var arg (ObjectType None),
    r1_stmts @ assign_rv_var r1,
    assign_rv_var arg))
  ], rv 
  
let translate_to_number_prim arg ctx =
  let rv = fresh_r () in
  let assign_rv_expr e = [Basic (Assignment (mk_assign rv (Expression e)))] in
  let assign_rv_num v = assign_rv_expr (Literal (Num v)) in
  let assign_rv_var var = assign_rv_expr (Var var) in
  Sugar (If (type_of_var arg UndefinedType,
    assign_rv_num nan, (* TODO *)
    [ Sugar (If (type_of_var arg NullType,
      assign_rv_num 0.0,
      [ Sugar (If (type_of_var arg BooleanType,
        [ Sugar (If (equal_bool_expr arg true, 
          assign_rv_num 1.0,
          assign_rv_num 0.0))
        ],
        [ Sugar (If (type_of_var arg NumberType,
          assign_rv_var arg,
          (* Must be StringType *)
          assign_rv_expr (UnaryOp (ToNumberOp, Var arg))))
        ]))
      ]))
    ])), rv
    
let translate_abstract_relation x y leftfirst ctx =
  let to_primitive_x, px = translate_to_primitive x (Some NumberType) ctx in
  let to_primitive_y, py = translate_to_primitive y (Some NumberType) ctx in
  let to_prim_stmts =
    if leftfirst then (to_primitive_x @ to_primitive_y) 
                 else (to_primitive_y @ to_primitive_x) in
  let to_number_x, nx = translate_to_number_prim px ctx in
  let to_number_y, ny = translate_to_number_prim py ctx in
  let rv = fresh_r () in
  let assign_rv e = [Basic (Assignment (mk_assign rv (Expression e)))] in
  to_prim_stmts @
  [ Sugar (If (and_expr (type_of_var px StringType) (type_of_var py StringType),
      assign_rv (BinOp (Var px, Comparison LessThan, Var py)),
      [ to_number_x; 
        to_number_y;
        Sugar (If (or_expr (equal_num_expr nx nan) (equal_num_expr ny nan),
          assign_rv (Literal Undefined),
          [ Sugar (If (or_expr 
                        (equal_exprs (Var nx) (Var ny))
                        (or_expr 
                          (and_expr (equal_num_expr nx 0.) (equal_num_expr ny (-0.))) 
                          (or_expr 
                            (and_expr (equal_num_expr nx (-0.)) (equal_num_expr ny 0.)) 
                            (or_expr 
                              (equal_num_expr nx infinity)
                              (equal_num_expr ny neg_infinity)))),
              assign_rv (Literal (Bool false)),
              [ Sugar (If (or_expr (equal_num_expr nx neg_infinity) (equal_num_expr ny infinity),
                  assign_rv (Literal (Bool true)),
                  assign_rv (BinOp (Var nx, Comparison LessThan, Var ny))))
              ]))
          ]))
      ]));
  ], rv
  
let translate_to_boolean arg ctx =
  let rv = fresh_r () in
  let assign_rv b = [Basic (Assignment (mk_assign rv (Expression (Literal (Bool b)))))] in
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
                      (equal_num_expr arg 0.0)))))),
    assign_rv false,
    assign_rv true)), rv
    
let translate_to_number arg ctx = 
  let r2 = fresh_r () in
  let to_primitive, primValue = translate_to_primitive arg (Some NumberType) ctx in
  let to_number, r1 = translate_to_number_prim r2 ctx in
  let rv = fresh_r () in
  let assign_rv_var var = Basic (Assignment (mk_assign rv (Expression (Var var)))) in
  let assign_r2_var var = [Basic (Assignment (mk_assign r2 (Expression (Var var))))] in
  [
    Sugar (If (type_of_var arg (ObjectType None),
      to_primitive @ (assign_r2_var primValue),
      (assign_r2_var arg)));
    to_number;
    assign_rv_var r1
  ], rv
    
let rec translate_to_string_prim arg ctx =
  let rv = fresh_r () in  
  let assign_rv_expr e = [Basic (Assignment (mk_assign rv (Expression e)))] in
  let assign_rv_str v = assign_rv_expr (Literal (String v)) in
  let assign_rv_var var = assign_rv_expr (Var var) in
  Sugar (If (type_of_var arg UndefinedType,
    assign_rv_str "undefined", (* TODO *)
    [ Sugar (If (type_of_var arg NullType,
      assign_rv_str "null",
      [ Sugar (If (type_of_var arg BooleanType,
        [ Sugar (If (equal_bool_expr arg true, 
          assign_rv_str "true",
          assign_rv_str "false"))
        ],
        [ Sugar (If (type_of_var arg StringType,
          assign_rv_var arg,
          (* Must be NumberType *)
          assign_rv_expr (UnaryOp (ToStringOp, Var arg))))
          ]))
        ]))
      ])), rv
      
let translate_to_string arg ctx = 
  let r2 = fresh_r () in
  let to_primitive, primValue = translate_to_primitive arg (Some StringType) ctx in
  let to_string, r1 = translate_to_string_prim r2 ctx in
  let rv = fresh_r () in
  let assign_rv_var var = Basic (Assignment (mk_assign rv (Expression (Var var)))) in
  let assign_r2_var var = [Basic (Assignment (mk_assign r2 (Expression (Var var))))] in
  [
    Sugar (If (type_of_var arg (ObjectType None),
      to_primitive @ (assign_r2_var primValue),
      (assign_r2_var arg)));
    to_string;
    (assign_rv_var r1)
  ], rv  
         
let translate_to_number_bin_op f op e1 e2 ctx =
  let r1_stmts, r1 = f e1 in
  let r2_stmts, r2 = translate_gamma r1 ctx in
  let r3_stmts, r3 = f e2 in
  let r4_stmts, r4 = translate_gamma r3 ctx in
  let r5_stmts, r5 = translate_to_number r2 ctx in
  let r6_stmts, r6 = translate_to_number r4 ctx in 
  let r7 = mk_assign_fresh_e (BinOp (Var r5, tr_bin_op op, Var r6)) in
    r1_stmts @ 
    r2_stmts @ 
    r3_stmts @ 
    r4_stmts @ 
    r5_stmts @
    r6_stmts @
    [Basic (Assignment r7)],
    r7.assign_left
        
let translate_bitwise_bin_op f op e1 e2 ctx =
  let r1_stmts, r1 = f e1 in
  let r2_stmts, r2 = translate_gamma r1 ctx in
  let r3_stmts, r3 = f e2 in
  let r4_stmts, r4 = translate_gamma r3 ctx in
  let r2_to_number, r2_number = translate_to_number r2 ctx in
  let r4_to_number, r4_number = translate_to_number r4 ctx in
  let r5 = mk_assign_fresh_e (UnaryOp (ToInt32Op, Var r2_number)) in
  let r6 = mk_assign_fresh_e (UnaryOp (ToInt32Op, Var r4_number)) in
  let r7 = mk_assign_fresh_e (BinOp (Var r5.assign_left, tr_bin_op op, Var r6.assign_left)) in
    r1_stmts @ 
    r2_stmts @ 
    r3_stmts @ 
    r4_stmts @ 
    r2_to_number @
    r4_to_number @
    [Basic (Assignment r5);
     Basic (Assignment r6);
     Basic (Assignment r7)
    ],
    r7.assign_left
    
let translate_bitwise_shift f op1 op2 op3 e1 e2 ctx = 
  let r1_stmts, r1 = f e1 in
  let r2_stmts, r2 = translate_gamma r1 ctx in
  let r3_stmts, r3 = f e2 in
  let r4_stmts, r4 = translate_gamma r3 ctx in
  let r2_to_number, r2_number = translate_to_number r2 ctx in
  let r4_to_number, r4_number = translate_to_number r4 ctx in
  let r5 = mk_assign_fresh_e (UnaryOp (op1, Var r2_number)) in
  let r6 = mk_assign_fresh_e (UnaryOp (op2, Var r4_number)) in
  let r7 = mk_assign_fresh_e (BinOp (Var r5.assign_left, Bitwise op3, Var r6.assign_left)) in
    r1_stmts @ 
    r2_stmts @ 
    r3_stmts @ 
    r4_stmts @ 
    r2_to_number @
    r4_to_number @
    [Basic (Assignment r5);
     Basic (Assignment r6);
     Basic (Assignment r7)
    ],
    r7.assign_left
  
let translate_regular_bin_op f op e1 e2 ctx =
  let r1_stmts, r1 = f e1 in
  let r2_stmts, r2 = translate_gamma r1 ctx in
  let r3_stmts, r3 = f e2 in
  let r4_stmts, r4 = translate_gamma r3 ctx in
  let rv = fresh_r () in
  let assign_rv rvar e = Basic (Assignment (mk_assign rvar (Expression e))) in 
  let exit_label = fresh_r () in
  let types_equal_stmts_1 = translate_strict_equality_comparison_types_equal r2 r4 rv in
  let y1_to_prim = fresh_r () in
  let to_primitive_y1, y1_prim = translate_to_primitive r4 None ctx in
  let x1_to_prim = fresh_r () in
  let to_primitive_x1, x1_prim = translate_to_primitive r2 None ctx in
  let x2_to_number = fresh_r () in
  let to_number_x2, x2_number = translate_to_number_prim x1_to_prim ctx in
  let y2_to_number = fresh_r () in
  let to_number_y2, y2_number = translate_to_number_prim y1_to_prim ctx in
  let y3 = fresh_r () in
  let to_number_y3, y3_number = translate_to_number_prim y2_to_number ctx in
  let x3 = fresh_r () in
  let to_number_x3, x3_number = translate_to_number_prim x2_to_number ctx in
  let types_equal_stmts_2 = translate_strict_equality_comparison_types_equal x3 y3 rv in
    r1_stmts @ 
    r2_stmts @ 
    r3_stmts @ 
    r4_stmts @ 
    [
      Sugar (If (equal_exprs (TypeOf (Var r2)) (TypeOf (Var r4)),
        types_equal_stmts_1 @ [Goto exit_label],
		    [ 
		      Sugar (If (type_of_var r4 (ObjectType None),
		        to_primitive_y1 @ [assign_rv y1_to_prim (Var y1_prim)],
		        [assign_rv y1_to_prim (Var r4)]));
		      Sugar (If (type_of_var r2 (ObjectType None),
		          to_primitive_x1 @ [assign_rv x1_to_prim (Var x1_prim)],
		          [assign_rv x1_to_prim (Var r2)]));
		      Sugar (If (type_of_var x1_to_prim BooleanType,
		        [ to_number_x2] @ [assign_rv x2_to_number (Var x2_number)],
            [ assign_rv x2_to_number (Var x1_to_prim)]));
		      Sugar (If (type_of_var y1_to_prim BooleanType,
		          [ to_number_y2] @ [assign_rv y2_to_number (Var y2_number)],
              [ assign_rv y2_to_number (Var y1_to_prim)]));
          Sugar (If (or_expr 
                    (and_expr (equal_null_expr x2_to_number) (equal_undef_expr y2_to_number)) 
                    (and_expr (equal_undef_expr x2_to_number) (equal_null_expr y2_to_number)),
            [assign_rv rv (Literal (Bool true))] @ [Goto exit_label],
            []));
          Sugar (If (and_expr (type_of_var x2_to_number NumberType) (type_of_var y2_to_number StringType),
              [ to_number_y3] @ [assign_rv y3 (Var y3_number)],
              [ assign_rv y3 (Var y2_to_number)]));
          Sugar (If (and_expr (type_of_var x2_to_number StringType) (type_of_var y2_to_number NumberType),
             [ to_number_x3] @ [assign_rv x3 (Var x3_number)],
             [ assign_rv x3 (Var x2_to_number)]));
          Sugar (If (equal_exprs (TypeOf (Var x3)) (TypeOf (Var y3)),
            types_equal_stmts_2 @ [Goto exit_label],
            [assign_rv rv (Literal (Bool false))] @ [Goto exit_label]))
      ]));        
    Label exit_label],
    rv
    
let translate_not_equal_bin_op f op e1 e2 ctx =
  let r1_stmts, r1 = translate_regular_bin_op f (Parser_syntax.Comparison (Parser_syntax.Equal)) e1 e2 ctx in
  let r2 = mk_assign_fresh (Expression (UnaryOp (Not, (Var r1)))) in
    r1_stmts @ 
    [
     Basic (Assignment r2)
    ], r2.assign_left
    
let translate_bin_op_plus f op e1 e2 ctx =
  let r1_stmts, r1 = f e1 in
  let r2_stmts, r2 = translate_gamma r1 ctx in
  let r3_stmts, r3 = f e2 in
  let r4_stmts, r4 = translate_gamma r3 ctx in
  let r5_stmts, lprim = translate_to_primitive r2 None ctx in
  let r6_stmts, rprim = translate_to_primitive r4 None ctx in
  let r7_stmt, lstring = translate_to_string_prim lprim ctx in
  let r8_stmt, rstring = translate_to_string_prim rprim ctx in  
  let r9_stmt, lnum = translate_to_number_prim lprim ctx in
  let r10_stmt, rnum = translate_to_number_prim rprim ctx in
  let rv = fresh_r () in
  let assign_rv_expr e = Basic (Assignment (mk_assign rv (Expression e))) in
    r1_stmts @ 
    r2_stmts @ 
    r3_stmts @ 
    r4_stmts @
    r5_stmts @
    r6_stmts @
    [ Sugar (If (or_expr 
                  (type_of_var lprim StringType)
                  (type_of_var rprim StringType),
      [r7_stmt; r8_stmt; assign_rv_expr (BinOp (Var lstring, Concat, Var rstring))],
      [r9_stmt; r10_stmt; assign_rv_expr (BinOp (Var lnum, Arith Plus, Var rnum))]))
    ], rv
  
   
let translate_bin_op_logical f e1 e2 bop ctx =
  let op = tr_boolean_op bop in
  let r1_stmts, r1 = f e1 in
  let r2_stmts, r2 = translate_gamma r1 ctx in
  let rv = fresh_r () in
  let r3_stmts, r3 = f e2 in
  let r4_stmts, r4 = translate_gamma r3 ctx in
  let to_boolean, r5 = translate_to_boolean r2 ctx in
    r1_stmts @ 
    r2_stmts @ 
    [ to_boolean;
      Sugar (If ((if (op = And) then (equal_bool_expr r5 false) else (equal_bool_expr r5 true)), 
        [Basic (Assignment (mk_assign rv (Expression (Var r2))))], 
	      (r3_stmts) @ 
	      r4_stmts @ 
	      [Basic (Assignment (mk_assign rv (Expression (Var r4))))]))
    ], rv
    
let unfold_spec_function sf =
  match sf with
    | GetValue e -> raise (PulpNotImplemented "Unfolding Spec Function")
    | PutValue (e1, e2) -> raise (PulpNotImplemented "Unfolding Spec Function")
    | Get e -> raise (PulpNotImplemented "Unfolding Spec Function")
    | Put (e1, e2) -> raise (PulpNotImplemented "Unfolding Spec Function")
    | HasProperty e -> raise (PulpNotImplemented "Unfolding Spec Function")
    | Delete e -> raise (PulpNotImplemented "Unfolding Spec Function")
    | DefaultValue e -> raise (PulpNotImplemented "Unfolding Spec Function")
    | ToPrimitive e -> raise (PulpNotImplemented "Unfolding Spec Function")
    | ToBoolean e -> raise (PulpNotImplemented "Unfolding Spec Function")
    | ToNumber e -> raise (PulpNotImplemented "Unfolding Spec Function")
    | ToInteger e -> raise (PulpNotImplemented "Unfolding Spec Function")
    | ToString e -> raise (PulpNotImplemented "Unfolding Spec Function")
    | ToObject e -> raise (PulpNotImplemented "Unfolding Spec Function")
    | CheckObjectCoercible e -> raise (PulpNotImplemented "Unfolding Spec Function")
    | IsCallable e -> raise (PulpNotImplemented "Unfolding Spec Function")
    | SameValue (e1, e2) -> raise (PulpNotImplemented "Unfolding Spec Function")
    | AbstractEquality (e1, e2) -> raise (PulpNotImplemented "Unfolding Spec Function")
    | StrictEquality (e1, e2) -> raise (PulpNotImplemented "Unfolding Spec Function")
    
let rec unfold_spec_functions stmts = 
  let f = unfold_spec_functions in
    List.flatten (List.map (fun stmt ->
      match stmt with
          | Sugar st -> 
            begin match st with
              | If (c, t1, t2) -> [Sugar (If (c, f t1, f t2))]
              | SpecFunction (v, sf) -> unfold_spec_function sf
            end
          | stmt -> [stmt]
  ) stmts)
  
let rec to_ivl_goto stmts = 
  let stmts = unfold_spec_functions stmts in
  List.flatten (List.map (fun stmt ->
	  match stmt with
	      | Sugar st -> 
	        begin match st with
	          | If (c, t1, t2) -> 
	            let label1 = fresh_r () in
	            let label2 = fresh_r () in
	            let label3 = fresh_r () in
	            let dt1 = to_ivl_goto t1 in
	            let dt2 = to_ivl_goto t2 in
	            [
	              GuardedGoto (c, label1, label2); 
	              Label label1
	            ] @ 
	            dt1 @ 
	            [
	              Goto label3; 
	              Label label2
	            ] @ 
	            dt2 @ 
	            [
	              Goto label3; 
	              Label label3
	            ]
            | SpecFunction _ -> raise (Invalid_argument "Spec Functions must have been unfolded")
	        end
	      | stmt -> [stmt]
  ) stmts)
  
let find_var_scope var env =
  try 
  let scope = List.find (fun scope ->
    List.exists (fun v -> v = var) scope.fun_bindings
    ) env in
  Var (function_scope_name (scope.func_id))
  with
    | Not_found -> Literal (LLoc Lg) 


let translate_literal exp : statement list * variable =
  match exp.Parser_syntax.exp_stx with
      (* Literals *)
      | Parser_syntax.Null ->
        begin 
          let assign = mk_assign_fresh_lit Null in 
          [Basic (Assignment assign)], assign.assign_left
        end
      | Parser_syntax.Bool b -> 
        begin 
          let assign = mk_assign_fresh_lit (Bool b) in 
          [Basic (Assignment assign)], assign.assign_left
        end
     | Parser_syntax.String s -> 
        begin 
          let assign = mk_assign_fresh_lit (String s) in 
          [Basic (Assignment assign)], assign.assign_left
        end
     | Parser_syntax.Num n -> 
        begin
          let assign = mk_assign_fresh_lit (Num n) in 
          [Basic (Assignment assign)], assign.assign_left
        end
      | _ -> raise (PulpInvalid ("Expected literal. Actual " ^ (Pretty_print.string_of_exp true exp)))

let translate_function_expression exp params ctx named =
  let fid = get_codename exp in
  let f_obj = mk_assign_fresh Obj in
  let prototype = mk_assign_fresh Obj in
  let scope = mk_assign_fresh Obj in
  
  let decl_stmts = match named with
    | None -> []
    | Some name ->
      let fid_decl = named_function_decl fid in
      let decl = mk_assign_fresh Obj in
        [Basic (Assignment decl);
         add_proto_null decl.assign_left;    
         Basic (Mutation (mk_mutation (Var decl.assign_left) (Literal (String name)) (Var f_obj.assign_left)));
         Basic (Mutation (mk_mutation (Var scope.assign_left) (Literal (String fid_decl)) (Var decl.assign_left)))
        ] in
    
  let env_stmts = Utils.flat_map (fun env -> 
  [
    Basic (Mutation (mk_mutation (Var scope.assign_left) (Literal (String env.func_id)) (Var (function_scope_name env.func_id))))
  ]) ctx.env_vars in
  
  [
    Basic (Assignment f_obj);
    Basic (Mutation (mk_mutation (Var f_obj.assign_left) (literal_builtin_field FClass) (Literal (String "Function"))));
    add_proto_value f_obj.assign_left Lfp;
    Basic (Assignment prototype); 
    add_proto_value prototype.assign_left Lop; 
    Basic (Mutation (mk_mutation (Var prototype.assign_left) (Literal (String "constructor")) (Var f_obj.assign_left)));
    Basic (Mutation (mk_mutation (Var f_obj.assign_left) (literal_builtin_field FPrototype) (Var prototype.assign_left)));
    Basic (Assignment scope);
    add_proto_null scope.assign_left
  ] @ 
  decl_stmts @
  env_stmts @ 
  [
    Basic (Mutation (mk_mutation (Var f_obj.assign_left) (literal_builtin_field FId) (Literal (String fid)))); 
    Basic (Mutation (mk_mutation (Var f_obj.assign_left) (literal_builtin_field FConstructId) (Literal (String fid))));
    Basic (Mutation (mk_mutation (Var f_obj.assign_left) (Literal (String "length")) (Literal (Num (float_of_int (List.length params)))))); 
    Basic (Mutation (mk_mutation (Var f_obj.assign_left) (literal_builtin_field FScope) (Var scope.assign_left))); 
  ], f_obj.assign_left 
  
let translate_has_instance f v ctx =
  let rv = fresh_r () in
  let get_stmts, o = translate_get f (literal_builtin_field FPrototype) in
  let proto = mk_assign_fresh (Lookup (Var v, literal_builtin_field FProto)) in
  let proto_o = mk_assign_fresh (ProtoO (Var proto.assign_left, Var o)) in
  [ Sugar (If (type_of_var v (ObjectType None), 
    get_stmts @
    [ Sugar (If (type_of_var o (ObjectType None),
      [ Basic (Assignment proto);
        Basic (Assignment proto_o);
        Basic (Assignment (mk_assign rv (Expression (Var proto_o.assign_left))))
      ],
      translate_error_throw Ltep ctx.throw_var ctx.label_throw))
    ],
    [Basic (Assignment (mk_assign rv (Expression (Literal (Bool false)))))]))
  ], rv
    
let translate_has_property o p =
  (* TODO use this in other places too *) 
  let rv = fresh_r () in  
  let assign_pi = mk_assign_fresh (ProtoF (Var o, p)) in 
	[ Basic (Assignment assign_pi);
	  Sugar (If (equal_empty_expr assign_pi.assign_left,
	    [Basic (Assignment (mk_assign rv (Expression(Literal (Bool false)))))],
	    [Basic (Assignment (mk_assign rv (Expression(Literal (Bool true)))))])) 
	], rv
  
let translate_inc_dec f e op ctx =
  let r1_stmts, r1 = f e in
  let r2_stmts, r2 = translate_gamma r1 ctx in
  let to_number_stmts, oldvalue = translate_to_number r2 ctx in
  let newvalue = mk_assign_fresh_e (BinOp (Var oldvalue, Arith op, (Literal (Num 1.0)))) in          
    r1_stmts @  
    [Sugar (If (and_expr (is_vref_expr r1)
                  (or_expr 
                  (equal_string_exprs (Field (Var r1)) "arguments") 
                  (equal_string_exprs (Field (Var r1)) "eval")), 
      translate_error_throw LSError ctx.throw_var ctx.label_throw, 
      r2_stmts @  
      to_number_stmts @
      [
        Basic (Assignment newvalue);
        translate_put_value r1 newvalue.assign_left ctx.throw_var ctx.label_throw
      ]))
    ], oldvalue, newvalue.assign_left


let rec translate_exp ctx exp : statement list * variable =
  let f = translate_exp ctx in 
  match exp.Parser_syntax.exp_stx with
      (* Literals *)
      | Parser_syntax.Null 
      | Parser_syntax.Bool _
      | Parser_syntax.String _  
      | Parser_syntax.Num _  -> translate_literal exp
      
      | Parser_syntax.This -> [], rthis
        
      | Parser_syntax.Var v -> 
        begin 
          let scope = find_var_scope v ctx.env_vars in
          let ref_assign = mk_assign_fresh_e (Ref (scope, Literal (String v) , VariableReference)) in
          [Basic (Assignment ref_assign)], ref_assign.assign_left         
        end
        
      | Parser_syntax.Obj xs ->
        begin
          (* TODO Make sure the behaviour is as in new Object() *)
          let r1 = mk_assign_fresh Obj in
          
          let stmts = List.map (fun (prop_name, prop_type, e) ->
            match prop_type with
              | Parser_syntax.PropbodyVal ->
                begin
                  let r2_stmts, r2 = f e in
                  let r3_stmts, r3 = translate_gamma r2 ctx in 
                  let propname_stmts, propname_expr = 
                    match prop_name with
                      | Parser_syntax.PropnameId s
                      | Parser_syntax.PropnameString s -> [],  Literal (String s)
                      | Parser_syntax.PropnameNum f -> 
                        begin
                          let f_var = mk_assign_fresh_e (Literal (Num f)) in
                          let propname_to_string, lvar = translate_to_string_prim f_var.assign_left ctx in 
                          [ Basic (Assignment f_var);
                            propname_to_string ], Var lvar
                        end in
                  r2_stmts @ 
                  r3_stmts @ 
                  propname_stmts @
                  [ Basic (Mutation (mk_mutation (Var r1.assign_left) propname_expr (Var r3)))] 
                   
                end
              | _ -> raise (PulpNotImplemented ("Getters and Setters are not yet implemented REF:11.1.5 Object Initialiser.Get.Set."))
            ) xs in
                           
            [
              Basic (Assignment r1);
              add_proto_value r1.assign_left Lop; 
              Basic (Mutation (mk_mutation (Var r1.assign_left) (literal_builtin_field FClass) (Literal (String "Object"))));
            ] @ 
            (List.flatten stmts), r1.assign_left
        end
        
      | Parser_syntax.Access (e, v) -> 
          let r1_stmts, r1 = f e in
          let r2_stmts, r2 = translate_gamma r1 ctx in
          let r4_stmts, r4 = translate_obj_coercible r2 ctx in
          let r5 = mk_assign_fresh_e (Ref (Var r2, Literal (String v), MemberReference)) in
            r1_stmts @ 
            r2_stmts @ 
            r4_stmts @
            [Basic (Assignment r5)], r5.assign_left
        
      | Parser_syntax.CAccess (e1, e2) ->
          let r1_stmts, r1 = f e1 in
          let r2_stmts, r2 = translate_gamma r1 ctx in
          let r3_stmts, r3 = f e2 in
          let r4_stmts, r4 = translate_gamma r3 ctx in
          let r5_stmts, r5 = translate_obj_coercible r2 ctx in
          let r4_to_string, r4_string = translate_to_string r4 ctx in
          let r6 = mk_assign_fresh_e (Ref (Var r2, Var r4_string, MemberReference)) in
            r1_stmts @ 
            r2_stmts @ 
            r3_stmts @ 
            r4_stmts @ 
            r5_stmts @ 
            r4_to_string @
            [Basic (Assignment r6)], r6.assign_left
            
      | Parser_syntax.New (e1, e2s) ->
        let stmts, r1, r2, arg_values = translate_call_construct_start f e1 e2s ctx true in
        let prototype = mk_assign_fresh (Lookup (Var r2, literal_builtin_field FPrototype)) in        
        let vthisproto = fresh_r () in
        let vthis = mk_assign_fresh Obj in
        let if3, call_lvar = translate_inner_call r2 vthis.assign_left arg_values ctx in (* TODO Construct vs. Call *)    
        let rv = fresh_r () in  
        let excep_label = fresh_r () in
        let exit_label = fresh_r () in
        
        (* TODO : move together with builtin function call *)
        let cid = mk_assign_fresh (Lookup (Var r2, literal_builtin_field FConstructId)) in 
	    let builtinconstr = mk_assign rv (BuiltinCall (mk_call 
		  (Var cid.assign_left) 
		  (Literal Empty)  (* No scope for builtin function *)
		  (Literal Empty)  (* No this either? *)
		  arg_values
          excep_label
		)) in
        
          stmts @ 
          [ Sugar (If (type_of_var r2 (ObjectType (Some Builtin)),
	          [ Basic (Assignment cid);
              Basic (Assignment builtinconstr);
              Goto exit_label;
					    Label excep_label;
					    Basic (Assignment (mk_assign ctx.throw_var (Expression (Var rv))));
					    Goto ctx.label_throw;
					    Label exit_label
            ],
	          [
	            Basic (Assignment prototype); 
	            Sugar (If (type_of_obj prototype.assign_left, 
	                [Basic (Assignment (mk_assign vthisproto (Expression (Var prototype.assign_left))))], 
	                [Basic (Assignment (mk_assign vthisproto (Expression (Literal (LLoc Lop)))))])); 
	            Basic (Assignment vthis);
	            add_proto_var vthis.assign_left vthisproto 
	          ] @
	          if3 @ 
	          [  Sugar (If (type_of_obj call_lvar, 
	                [Basic (Assignment (mk_assign rv (Expression (Var call_lvar))))], 
	                [Basic (Assignment (mk_assign rv (Expression (Var vthis.assign_left))))]))
	          ]))
          ], rv
        
      | Parser_syntax.Call (e1, e2s) ->
        let stmts, r1, r2, arg_values = translate_call_construct_start f e1 e2s ctx false in
              let vthis = fresh_r () in
              let assign_vthis_und = Basic (Assignment (mk_assign vthis (Expression (Literal Undefined)))) in
              let if5, call = translate_inner_call r2 vthis arg_values ctx in
          stmts @ 
          [
            Sugar (If (is_ref_expr r1, 
                [
                  Sugar (If (is_vref_expr r1, 
                    [assign_vthis_und], 
                    [
                      Basic (Assignment (mk_assign vthis (Expression (Base (Var r1)))))
                    ]))
                ],
                [assign_vthis_und]))
          ] @
          if5, call
          
      | Parser_syntax.AnnonymousFun (_, params, _) ->
        translate_function_expression exp params ctx None
        
      | Parser_syntax.NamedFun (_, name, params, _) -> 
        translate_function_expression exp params ctx (Some name)
          
      | Parser_syntax.Unary_op (op, e) ->
        begin match op with 
          | Parser_syntax.Not ->
            let r1_stmts, r1 = f e in
            let r2_stmts, r2 = translate_gamma r1 ctx in
            let rv = fresh_r () in 
            let to_boolean, r3 = translate_to_boolean r2 ctx in
            let if1 = 
              Sugar (If (equal_bool_expr r3 false, 
                [
                  Basic (Assignment (mk_assign rv (Expression (Literal (Bool true)))))
                ], 
                [
                  Basic (Assignment (mk_assign rv (Expression (Literal (Bool false)))))
                ])) in
                r1_stmts @
            r2_stmts @
            [to_boolean; if1], rv
          | Parser_syntax.TypeOf -> 
            begin
              let rv = fresh_r () in
              let r1_stmts, r1 = f e in
              let base = mk_assign_fresh (Expression (Base (Var r1))) in
              let value = fresh_r () in
              let r2_stmts, r2 = translate_gamma r1 ctx in
              let hasfield = mk_assign_fresh (HasField (Var value, literal_builtin_field FId)) in
              let exit_label = fresh_r () in
              let proto = mk_assign_fresh (ProtoF (Var base.assign_left, Field (Var r1))) in
              let if_lg_undefined = and_expr (equal_expr base.assign_left (Literal (LLoc Lg)))
                                             (equal_empty_expr proto.assign_left) in
              let assign_rv v = 
                [Basic (Assignment (mk_assign rv (Expression (Literal (String v)))));
                 Goto exit_label] in
              r1_stmts @
              [
                Sugar (If (is_ref_expr r1,
                [
                  Basic (Assignment base);
                  Basic (Assignment proto);
                  Sugar (If (or_expr (equal_undef_expr base.assign_left) if_lg_undefined,
                   assign_rv "undefined",
                   r2_stmts @
                   [
                    Basic (Assignment (mk_assign value (Expression (Var r2))))
                   ]))
                ],
                [Basic (Assignment (mk_assign value (Expression (Var r1))))]));
                Sugar (If (type_of_var value UndefinedType,
                  assign_rv "undefined",
                  [Sugar (If (type_of_var value NullType,
                    assign_rv "object",
                    [Sugar (If (type_of_var value BooleanType,
                      assign_rv "boolean",
                      [Sugar (If (type_of_var value NumberType,
                        assign_rv "number",
                        [Sugar (If (type_of_var value StringType,
                          assign_rv "string",
                          (* Must be an object *)
                          [ Basic (Assignment hasfield);
                            Sugar (If (equal_bool_expr hasfield.assign_left true,
                              assign_rv "function",
                              assign_rv "object"))
                          ]))
                        ]))
                      ]))
                    ]))
                  ]));
                Label exit_label;
              ], rv
            end
					| Parser_syntax.Positive -> 
            let r1_stmts, r1 = f e in
            let r2_stmts, r2 = translate_gamma r1 ctx in
            let r3_stmts, r3 = translate_to_number r2 ctx in
            r1_stmts @
            r2_stmts @
            r3_stmts, r3
					| Parser_syntax.Negative -> 
            let r1_stmts, r1 = f e in
            let r2_stmts, r2 = translate_gamma r1 ctx in
            let r3_stmts, r3 = translate_to_number r2 ctx in
            let rv = fresh_r () in
            let assign_rv n = [Basic (Assignment (mk_assign rv (Expression n)))] in
            let negative = mk_assign_fresh_e (UnaryOp (Negative, (Var r3))) in
            r1_stmts @
            r2_stmts @
            r3_stmts @
            [ Sugar (If (equal_num_expr r3 nan,
               assign_rv (Literal (Num nan)),
               [Basic (Assignment negative)] @
               assign_rv (Var negative.assign_left)))
            ], rv
		  | Parser_syntax.Pre_Decr -> 
            let stmts, _, newvalue = translate_inc_dec f e Minus ctx
            in stmts, newvalue
					| Parser_syntax.Post_Decr -> 
            let stmts, oldvalue, _ = translate_inc_dec f e Minus ctx
            in stmts, oldvalue
					| Parser_syntax.Pre_Incr -> 
            let stmts, _, newvalue = translate_inc_dec f e Plus ctx
            in stmts, newvalue
					| Parser_syntax.Post_Incr -> 
            let stmts, oldvalue, _ = translate_inc_dec f e Plus ctx
            in stmts, oldvalue
		      | Parser_syntax.Bitnot -> 
            let r1_stmts, r1 = f e in
            let r2_stmts, r2 = translate_gamma r1 ctx in
            let r2_to_number, r2_number = translate_to_number r2 ctx in
            let r3 = mk_assign_fresh_e (UnaryOp (ToInt32Op, Var r2_number)) in
            let r4 = mk_assign_fresh_e (UnaryOp (BitwiseNot, Var r3.assign_left)) in
            r1_stmts @
            r2_stmts @
            r2_to_number @
            [Basic (Assignment r3);
             Basic (Assignment r4)], r4.assign_left
		      | Parser_syntax.Void -> 
            let r1_stmts, r1 = f e in
            let r2_stmts, _ = translate_gamma r1 ctx in
            let rv = mk_assign_fresh_e (Literal Undefined) in
            r1_stmts @
            r2_stmts @
            [Basic (Assignment rv)], rv.assign_left
        end 
        
      | Parser_syntax.Delete e ->
        let r1_stmts, r1 = f e in
        let rv = fresh_r () in
        let assign_rv_true = mk_assign rv (Expression (Literal (Bool true))) in
        let r4 = mk_assign_fresh_e (Base (Var r1)) in 
        let gotothrow = translate_error_throw LSError ctx.throw_var ctx.label_throw in
        let r3 = mk_assign_fresh_e (Field (Var r1)) in      
        let r2 = mk_assign_fresh (HasField (Var r4.assign_left, Var r3.assign_left)) in
        (* TODO : Changes when we add attributes *)
        let r5 = mk_assign_fresh (HasField (Var r4.assign_left, literal_builtin_field FId)) in
          r1_stmts @ 
          [
            Sugar (If (is_ref_expr r1, 
                [ Basic (Assignment r4);
                  Sugar (If (equal_undef_expr r4.assign_left, 
                    gotothrow, 
                    [])); 
                  Sugar (If (is_vref_expr r1, 
                    gotothrow, 
                    [])); 
                  Basic (Assignment r3);  
                  Basic (Assignment r2); 
                  Sugar (If (equal_bool_expr r2.assign_left false, 
                    [Basic (Assignment assign_rv_true)], 
                    [
                      Basic (Assignment r5); 
                      Sugar (If (and_expr 
                                (equal_expr r3.assign_left (literal_builtin_field FPrototype)) 
                                (equal_bool_expr r5.assign_left true), 
                        translate_error_throw Ltep ctx.throw_var ctx.label_throw, 
                        [ Basic (Assignment (mk_assign_fresh (Deallocation (Var r4.assign_left, Var r3.assign_left))));
                          Basic (Assignment assign_rv_true)
                        ]))
                    ]))
                ], 
                [Basic (Assignment assign_rv_true)])); 
          ], rv
          
					
      | Parser_syntax.BinOp (e1, op, e2) ->
        (* TODO : conversions etc. *)
        begin match op with
          | Parser_syntax.Comparison cop ->
            begin match cop with
              | Parser_syntax.Equal -> translate_regular_bin_op f op e1 e2 ctx
              | Parser_syntax.NotEqual -> translate_not_equal_bin_op f op e1 e2 ctx
						  | Parser_syntax.TripleEqual -> 
                  let r1_stmts, r1 = f e1 in
								  let r2_stmts, r2 = translate_gamma r1 ctx in
								  let r3_stmts, r3 = f e2 in
								  let r4_stmts, r4 = translate_gamma r3 ctx in
								  let r5, rv = translate_strict_equality_comparison r2 r4 in
								    r1_stmts @ 
								    r2_stmts @ 
								    r3_stmts @ 
								    r4_stmts @ 
								    [r5], rv
						  | Parser_syntax.NotTripleEqual ->
                  let r1_stmts, r1 = f e1 in
                  let r2_stmts, r2 = translate_gamma r1 ctx in
                  let r3_stmts, r3 = f e2 in
                  let r4_stmts, r4 = translate_gamma r3 ctx in
                  let r5, rv = translate_strict_equality_comparison r2 r4 in
                  let r6 = mk_assign_fresh (Expression (UnaryOp (Not, (Var rv)))) in
                    r1_stmts @ 
                    r2_stmts @ 
                    r3_stmts @ 
                    r4_stmts @ 
                    [r5;
                     Basic (Assignment r6)
                    ], r6.assign_left
						  | Parser_syntax.Lt -> 
                  let r1_stmts, r1 = f e1 in
								  let r2_stmts, r2 = translate_gamma r1 ctx in
								  let r3_stmts, r3 = f e2 in
								  let r4_stmts, r4 = translate_gamma r3 ctx in
                  let r5_stmts, r5 = translate_abstract_relation r2 r4 true ctx in
                  let rv = fresh_r() in
                  let assign_rv v = Basic (Assignment (mk_assign rv (Expression v))) in                  
								    r1_stmts @ 
								    r2_stmts @ 
								    r3_stmts @ 
								    r4_stmts @
                    r5_stmts @ 
								    [Sugar (If (equal_undef_expr r5, 
                      [assign_rv (Literal (Bool false))], 
                      [assign_rv (Var r5)]))
                    ], rv
						  | Parser_syntax.Le -> 
                  let r1_stmts, r1 = f e1 in
                  let r2_stmts, r2 = translate_gamma r1 ctx in
                  let r3_stmts, r3 = f e2 in
                  let r4_stmts, r4 = translate_gamma r3 ctx in
                  let r5_stmts, r5 = translate_abstract_relation r4 r2 false ctx in
                  let rv = fresh_r() in
                  let assign_rv v = Basic (Assignment (mk_assign rv (Expression v))) in                  
                    r1_stmts @ 
                    r2_stmts @ 
                    r3_stmts @ 
                    r4_stmts @
                    r5_stmts @ 
                    [Sugar (If (or_expr (equal_bool_expr r5 true) (equal_undef_expr r5), 
                      [assign_rv (Literal (Bool false))], 
                      [assign_rv (Literal (Bool true))]))
                    ], rv
						  | Parser_syntax.Gt -> 
                  let r1_stmts, r1 = f e1 in
                  let r2_stmts, r2 = translate_gamma r1 ctx in
                  let r3_stmts, r3 = f e2 in
                  let r4_stmts, r4 = translate_gamma r3 ctx in
                  let r5_stmts, r5 = translate_abstract_relation r4 r2 false ctx in
                  let rv = fresh_r() in
                  let assign_rv v = Basic (Assignment (mk_assign rv (Expression v))) in                  
                    r1_stmts @ 
                    r2_stmts @ 
                    r3_stmts @ 
                    r4_stmts @
                    r5_stmts @ 
                    [Sugar (If (equal_undef_expr r5, 
                      [assign_rv (Literal (Bool false))], 
                      [assign_rv (Var r5)]))
                    ], rv
						  | Parser_syntax.Ge -> 
                  let r1_stmts, r1 = f e1 in
                  let r2_stmts, r2 = translate_gamma r1 ctx in
                  let r3_stmts, r3 = f e2 in
                  let r4_stmts, r4 = translate_gamma r3 ctx in
                  let r5_stmts, r5 = translate_abstract_relation r2 r4 true ctx in
                  let rv = fresh_r() in
                  let assign_rv v = Basic (Assignment (mk_assign rv (Expression v))) in                  
                    r1_stmts @ 
                    r2_stmts @ 
                    r3_stmts @ 
                    r4_stmts @
                    r5_stmts @ 
                    [Sugar (If (or_expr (equal_bool_expr r5 true) (equal_undef_expr r5), 
                      [assign_rv (Literal (Bool false))], 
                      [assign_rv (Literal (Bool true))]))
                    ], rv
			 | Parser_syntax.In -> 
                let r1_stmts, r1 = f e1 in
                let r2_stmts, r2 = translate_gamma r1 ctx in
                let r3_stmts, r3 = f e2 in
                let r4_stmts, r4 = translate_gamma r3 ctx in
                let r5_stmts, r5 = translate_to_string r2 ctx in
                let r6_stmts, r6 = translate_has_property r4 (Var r5) in
                r1_stmts @ 
                r2_stmts @ 
                r3_stmts @ 
                r4_stmts @
                [ Sugar (If (lessthan_exprs (TypeOf (Var r4)) (Literal (Type (ObjectType None))), 
                    r5_stmts @ r6_stmts,
                    translate_error_throw Ltep ctx.throw_var ctx.label_throw))
                ], r6
			| Parser_syntax.InstanceOf -> 
                let r1_stmts, r1 = f e1 in
                let r2_stmts, r2 = translate_gamma r1 ctx in
                let r3_stmts, r3 = f e2 in
                let r4_stmts, r4 = translate_gamma r3 ctx in
                let hasfield = mk_assign_fresh (HasField (Var r4, literal_builtin_field FId)) in
                let gotothrow = translate_error_throw Ltep ctx.throw_var ctx.label_throw in
                let r5_stmts, r5 = translate_has_instance r4 r2 ctx in
                r1_stmts @ 
                r2_stmts @ 
                r3_stmts @ 
                r4_stmts @
                [ Sugar (If (lessthan_exprs (TypeOf (Var r4)) (Literal (Type (ObjectType None))), 
                    [ Basic (Assignment hasfield);
                      Sugar (If (equal_bool_expr hasfield.assign_left false, (* [[HasInstance]] *)
                      gotothrow, 
                      r5_stmts))
                    ],
                    gotothrow))
                ], r5
                
            end
          | Parser_syntax.Arith aop -> 
            begin match aop with
              | Parser_syntax.Plus -> translate_bin_op_plus f op e1 e2 ctx
              | Parser_syntax.Minus
              | Parser_syntax.Times
              | Parser_syntax.Div 
              | Parser_syntax.Mod -> translate_to_number_bin_op f op e1 e2 ctx
						  | Parser_syntax.Ursh -> translate_bitwise_shift f ToUint32Op ToUint32Op UnsignedRightShift e1 e2 ctx
						  | Parser_syntax.Lsh -> translate_bitwise_shift f ToInt32Op ToUint32Op LeftShift e1 e2 ctx
						  | Parser_syntax.Rsh -> translate_bitwise_shift f ToInt32Op ToUint32Op SignedRightShift e1 e2 ctx
						  | Parser_syntax.Bitand 
						  | Parser_syntax.Bitor 
						  | Parser_syntax.Bitxor -> translate_bitwise_bin_op f op e1 e2 ctx
            end
          | Parser_syntax.Boolean bop -> 
            begin match bop with
              | Parser_syntax.And -> translate_bin_op_logical f e1 e2 bop ctx
              | Parser_syntax.Or -> translate_bin_op_logical f e1 e2 bop ctx
            end
        end
        
      | Parser_syntax.Assign (e1, e2) ->
        begin
          let r1_stmts, r1 = f e1 in
          let r2_stmts, r2 = f e2 in
          let r3_stmts, r3 = translate_gamma r2 ctx in
          let r4 = mk_assign_fresh_e (Field (Var r1)) in
          let gotothrow = translate_error_throw Lrep ctx.throw_var ctx.label_throw in
          
            r1_stmts @
            r2_stmts @
            r3_stmts @
            [
              Sugar (If (is_vref_expr r1, 
                    [
                      Basic (Assignment r4);
                      Sugar (If (or_expr 
                             (equal_string_expr r4.assign_left "arguments") 
                             (equal_string_expr r4.assign_left "eval"), gotothrow, []));
                    ], 
                    []))
            ] @
            [translate_put_value r1 r3 ctx.throw_var ctx.label_throw], r3
        end
      
      | Parser_syntax.Array _ -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:11.1.4 Array Initialiser.")))
      | Parser_syntax.ConditionalOp (e1, e2, e3) ->
        let r1_stmts, r1 = f e1 in
        let r2_stmts, r2 = translate_gamma r1 ctx in
        let r3_stmts, r3 = f e2 in
        let r4_stmts, r4 = translate_gamma r3 ctx in
        let r5_stmts, r5 = f e3 in
        let r6_stmts, r6 = translate_gamma r5 ctx in
        let to_boolean, r7 = translate_to_boolean r2 ctx in
        let rv = fresh_r () in     
          r1_stmts @ 
          r2_stmts @ 
          [ to_boolean;
            Sugar (If (equal_bool_expr r7 true, 
                r3_stmts @ 
                r4_stmts @
                [Basic (Assignment (mk_assign rv (Expression (Var r4))))], 
                r5_stmts @ 
                r6_stmts @
                [Basic (Assignment (mk_assign rv (Expression (Var r6))))]))
          ], rv
      | Parser_syntax.AssignOp (e1, aop, e2) -> 
          let r1_stmts, r1 = f e1 in
				  let r2_stmts, r2 = translate_gamma r1 ctx in
				  let r3_stmts, r3 = f e2 in
				  let r4_stmts, r4 = translate_gamma r3 ctx in
				  let r5 = mk_assign_fresh_e (BinOp (Var r2, tr_bin_op (Parser_syntax.Arith aop), Var r4)) in
          let field = mk_assign_fresh_e (Field (Var r1)) in
				    r1_stmts @ 
				    r2_stmts @ 
				    r3_stmts @ 
				    r4_stmts @ 
				    [Basic (Assignment r5);
             Sugar (If (type_of_vref_var r1,
		          [Basic (Assignment field);
               Sugar (If (or_expr 
                             (equal_string_expr field.assign_left "arguments") 
                             (equal_string_expr field.assign_left "eval"), 
                 translate_error_throw LSError ctx.throw_var ctx.label_throw, 
                 []))
              ],
		          []));
              translate_put_value r1 r5.assign_left ctx.throw_var ctx.label_throw
            ],
				    r5.assign_left

      | Parser_syntax.Comma (e1, e2) -> 
        let r1_stmts, r1 = f e1 in
        let r2_stmts, _ = translate_gamma r1 ctx in
        let r3_stmts, r3 = f e2 in
        let r4_stmts, r4 = translate_gamma r3 ctx in
          r1_stmts @ 
          r2_stmts @ 
          r3_stmts @ 
          r4_stmts, r4
          
      | Parser_syntax.RegExp _ -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:7.8.5 Regular Expression Literals.")))   

      (*Statements*)
      | Parser_syntax.Block _
      | Parser_syntax.Script _ 
      | Parser_syntax.VarDec _
      | Parser_syntax.Skip
      | Parser_syntax.If _
      | Parser_syntax.While _
      | Parser_syntax.Return _
      | Parser_syntax.DoWhile _
      | Parser_syntax.For _
      | Parser_syntax.ForIn _
      | Parser_syntax.Continue _
      | Parser_syntax.Break _
      | Parser_syntax.With _
      | Parser_syntax.Switch _  
      | Parser_syntax.Label _
      | Parser_syntax.Throw _
      | Parser_syntax.Try _    
      | Parser_syntax.Debugger -> raise (PulpInvalid ("Expected expression. Actual " ^ (Pretty_print.string_of_exp true exp)))

let translate_block es f ret_f =
    let compiled_stmts = List.map 
			(fun stmt ->
				let compiled_stmt, _ = f stmt in 
					compiled_stmt) es in 
    List.flatten compiled_stmts, ret_f

let rec translate_stmt ctx labelset exp : statement list * variable =
  (*Printf.printf ("Translating stmt %s with break labels %s") (Pretty_print.string_of_exp false exp) (string_of_break_continue_labels ctx);
  Printf.printf ("\n labelset %s \n") (String.concat ";" labelset);*)
  let f = translate_stmt ctx [] in 
	let ret_def = ctx.stmt_return_var in 
  match exp.Parser_syntax.exp_stx with
        (* Literals *)
      | Parser_syntax.Null 
      | Parser_syntax.Bool _
      | Parser_syntax.String _  
      | Parser_syntax.Num _
      
      (* Expressions *) 
      | Parser_syntax.This
      | Parser_syntax.Var _
      | Parser_syntax.Obj _
      | Parser_syntax.Access _
      | Parser_syntax.CAccess _
      | Parser_syntax.New _
      | Parser_syntax.Call _
      | Parser_syntax.Unary_op _ 
      | Parser_syntax.Delete _ 
      | Parser_syntax.BinOp _ 
      | Parser_syntax.Assign _  
      | Parser_syntax.Array _
      | Parser_syntax.ConditionalOp _
      | Parser_syntax.AssignOp _
      | Parser_syntax.Comma _ 
      | Parser_syntax.RegExp _  -> 
        let stmts, r1 = translate_exp ctx exp in
        let gamma_stmts, r2  = translate_gamma r1 ctx in
				let ret_val_stmts = [ 
          Sugar (If (equal_empty_expr r2, 
            [ ], 
            [
              Basic (Assignment (mk_assign ret_def (Expression (Var r2))))
            ]))] in 
        stmts @ gamma_stmts @ ret_val_stmts, ret_def

      | Parser_syntax.AnnonymousFun _
      | Parser_syntax.NamedFun _ -> raise (PulpInvalid ("Expected statement. Actual " ^ (Pretty_print.string_of_exp true exp)))
         (* If a function appears in the middle of a statement, it shall not be interpreted as an expression function, but as a function declaration *)
         (* NOTE in spec p.86 *)
         (* ... It is recommended that ECMAScript implementations either disallow this usage of FunctionDeclaration or issue a warning *)

      (*Statements*)
      | Parser_syntax.Script _ -> raise (PulpInvalid ("Expected Statememnt. Got Script"))
      | Parser_syntax.Block es -> translate_block es f ret_def

      | Parser_syntax.VarDec vars ->
        let result = List.map (fun var ->
          match var with
            | (v, Some exp) -> translate_exp ctx ({exp with Parser_syntax.exp_stx = (Parser_syntax.Assign ({exp with Parser_syntax.exp_stx = Parser_syntax.Var v}, exp))})
            | (v, None) -> f ({exp with Parser_syntax.exp_stx = Parser_syntax.Skip})
          ) vars in
        let stmts, _ = List.split result in
        let empty = mk_assign_fresh_lit Empty in
        (List.flatten stmts) @ [Basic (Assignment empty)], empty.assign_left

      | Parser_syntax.Skip -> 
        let r1 = mk_assign_fresh_lit Empty in
        [Basic (Assignment r1)], r1.assign_left 
        
      | Parser_syntax.If (e1, e2, e3) ->
        let r1_stmts, r1 = translate_exp ctx e1 in
        let r2_stmts, r2 = translate_gamma r1 ctx in
        let r3_stmts, r3 = f e2 in
        let to_boolean, r5 = translate_to_boolean r2 ctx in
        let elsebranch = match e3 with
          | Some e3 -> 
            let r4_stmts, r4 = f e3 in
            r4_stmts
          | None -> [] in      
          r1_stmts @ 
          r2_stmts @ 
          [ to_boolean;
            Sugar (If (equal_bool_expr r5 true, 
                r3_stmts, 
                elsebranch))
          ], ret_def
           
      | Parser_syntax.While (e1, e2) ->
        let r1_stmts, r1 = translate_exp ctx e1 in
        let r2_stmts, r2 = translate_gamma r1 ctx in
        let continue = fresh_r () in
        let break = fresh_r () in
        let new_ctx = {ctx with
          label_continue = (("", continue) :: (List.map (fun l -> (l, continue)) labelset)) @ ctx.label_continue;
          label_break = (("", break) :: (List.map (fun l -> (l, break)) labelset)) @ ctx.label_break
        } in
        let r3_stmts, r3 = translate_stmt new_ctx [] e2 in
        let to_boolean, r4 = translate_to_boolean r2 ctx in
          [
            Label continue
          ] @ 
          r1_stmts @ 
          r2_stmts @ 
          [ to_boolean;
            Sugar (If (equal_bool_expr r4 true, 
                r3_stmts @ 
                [ 
                  Goto continue
                ], 
                
                []));
            Label break
          ], ret_def
          
      | Parser_syntax.DoWhile (e1, e2) -> 
        let iterating = fresh_r () in
        let label1 = fresh_r () in
        let continue = fresh_r () in
        let break = fresh_r () in
        let new_ctx = {ctx with
          label_continue = (("", continue) :: (List.map (fun l -> (l, continue)) labelset)) @ ctx.label_continue;
          label_break = (("", break) :: (List.map (fun l -> (l, break)) labelset)) @ ctx.label_break
        } in
        let r3_stmts, r3 = translate_stmt new_ctx [] e1 in
        let r1_stmts, r1 = translate_exp ctx e2 in
        let r2_stmts, r2 = translate_gamma r1 ctx in
        let to_boolean, r4 = translate_to_boolean r2 ctx in
          [
            Basic (Assignment (mk_assign iterating (Expression (Literal (Bool true)))));
            Label label1;
            Sugar (If (equal_bool_expr iterating true, 
                r3_stmts @ 
                [ 
                  Label continue
                ] @
                r1_stmts @ 
                r2_stmts @ 
                [ to_boolean;    
                  Sugar (If (equal_bool_expr r4 false,
                    [Basic (Assignment (mk_assign iterating (Expression (Literal (Bool false)))))],
                    []));
                  Goto label1
                ],                
                []));
            Label break;
          ], ret_def

        
      | Parser_syntax.Return e ->
        let stmts, rv = match e with
          | None -> 
            let und_assign = mk_assign_fresh_lit Undefined in
            [Basic (Assignment und_assign)], und_assign.assign_left
          | Some e -> 
            let r1_stmts, r1 = translate_exp ctx e in
            let r2_stmts, r2 = translate_gamma r1 ctx in
            r1_stmts @ r2_stmts, r2
         in
        let assignr = mk_assign ctx.return_var (Expression (Var rv)) in
          stmts @ 
          [
            Basic (Assignment assignr); 
            Goto ctx.label_return
          ], ctx.return_var
           
      | Parser_syntax.Try (e1, Some (id, e2), Some e3) ->
        let catch_label = "catch." ^ fresh_r () in
        let finally_label = "finally." ^ fresh_r () in
        let return_finally_label = "finally." ^ fresh_r () in
        let throw_finally_label = "finally." ^ fresh_r () in
        let continue_finally_label = List.map (fun (l,c) -> (l, "finally." ^ fresh_r ())) ctx.label_continue in
        let break_finally_label = List.map (fun (l,c) -> (l, "finally." ^ fresh_r ())) ctx.label_break in  
        let exit_label = fresh_r () in
        let throw_var = fresh_r () in
        let new_ctx = {ctx with 
          label_throw = catch_label; 
          label_return = return_finally_label; 
          throw_var = throw_var;
          label_continue = continue_finally_label;
          label_break = break_finally_label;
        } in
        let r1_stmts, r1 = translate_stmt new_ctx [] e1 in
        
        let catch_id = "catch" ^ fresh_r () in
        let catch_scope = catch_id ^ "_scope" in
        
        let catch_ctx = {ctx with 
          env_vars = (make_ctx_vars catch_id [id]) :: ctx.env_vars;
          label_throw = throw_finally_label;
          label_return = return_finally_label;          
          label_continue = continue_finally_label;
          label_break = break_finally_label;
        } in
        let r2_stmts, r2 = translate_stmt catch_ctx [] e2 in
        let r3_stmts, r3 = f e3 in
        
        let continue_finally_stmts = List.map (fun ((_, c1), (_, c2)) ->
          [Label c1] @
          r3_stmts @
          [Goto c2]
        ) (List.combine continue_finally_label ctx.label_continue) in
        
        let break_finally_stmts = List.map (fun ((_, b1), (_, b2)) ->
          [Label b1] @
          r3_stmts @
          [Goto b2]
        ) (List.combine break_finally_label ctx.label_break) in
            
        r1_stmts @
        [
          Goto finally_label;
          Label catch_label;
          Basic (Assignment (mk_assign catch_scope Obj));
          add_proto_null catch_scope;
          Basic (Mutation (mk_mutation (Var catch_scope) (Literal (String id)) (Var throw_var)))
        ] @
        r2_stmts @
        [
          Goto finally_label;
          Label finally_label;
        ] @
        r3_stmts @
        [
          Goto exit_label;
          Label return_finally_label      
        ] @
        r3_stmts @
        [
          Goto ctx.label_return;
          Label throw_finally_label      
        ] @
        r3_stmts @
        [
          Goto ctx.label_throw
        ] @
        List.flatten continue_finally_stmts @
        List.flatten break_finally_stmts @
        [  Label exit_label
        ], ret_def
        
      | Parser_syntax.Try (e1, None, Some e3) ->
        let return_finally_label = "finally." ^ fresh_r () in
        let throw_finally_label = "finally." ^ fresh_r () in
        let continue_finally_label = List.map (fun (l,c) -> (l, "finally." ^ fresh_r ())) ctx.label_continue in
        let break_finally_label = List.map (fun (l,c) -> (l, "finally." ^ fresh_r ())) ctx.label_break in  
        let exit_label = fresh_r () in
        let new_ctx = {ctx with 
          label_throw = throw_finally_label; 
          label_return = return_finally_label;
          label_continue = continue_finally_label;
          label_break = break_finally_label;
        } in
        let r1_stmts, r1 = translate_stmt new_ctx [] e1 in
        let r3_stmts, r3 = f e3 in
        
        let continue_finally_stmts = List.map (fun ((_, c1), (_, c2)) ->
          [Label c1] @
          r3_stmts @
          [Goto c2]
        ) (List.combine continue_finally_label ctx.label_continue) in
        
        let break_finally_stmts = List.map (fun ((_, b1), (_, b2)) ->
          [Label b1] @
          r3_stmts @
          [Goto b2]
        ) (List.combine break_finally_label ctx.label_break) in
            
        r1_stmts @
        r3_stmts @
        [
          Goto exit_label;
          Label return_finally_label      
        ] @
        r3_stmts @
        [
          Goto ctx.label_return;
          Label throw_finally_label      
        ] @
        r3_stmts @
        [  Goto ctx.label_throw] @
        List.flatten continue_finally_stmts @
        List.flatten break_finally_stmts @
        [  Label exit_label], ret_def
        
      | Parser_syntax.Try (e1, Some (id, e2), None) ->
        let catch_label = "catch." ^ fresh_r () in
        let exit_label = fresh_r () in
        let throw_var = fresh_r () in
        let new_ctx = {ctx with label_throw = catch_label; throw_var = throw_var} in
        let r1_stmts, r1 = translate_stmt new_ctx [] e1 in
        
        let catch_id = "catch" ^ fresh_r () in
        let catch_scope = catch_id ^ "_scope" in
        
        let catch_ctx = {ctx with 
          env_vars = (make_ctx_vars catch_id [id]) :: ctx.env_vars;
        } in
        let r2_stmts, r2 = translate_stmt catch_ctx [] e2 in
            
        r1_stmts @
        [
          Goto exit_label;
          Label catch_label;
          Basic (Assignment (mk_assign catch_scope Obj));
          add_proto_null catch_scope;
          Basic (Mutation (mk_mutation (Var catch_scope) (Literal (String id)) (Var throw_var)))
        ] @
        r2_stmts @
        [
          Goto exit_label;
          Label exit_label;
        ], ret_def
        
      | Parser_syntax.Try _ -> raise (PulpInvalid "Try _ None None")
        
      | Parser_syntax.Throw e ->
        let r1_stmts, r1 = translate_exp ctx e in
        let r2_stmts, r2 = translate_gamma r1 ctx in 
        
        r1_stmts @ 
        r2_stmts @
        [ Basic (Assignment (mk_assign ctx.throw_var (Expression (Var r2))));
          Goto ctx.label_throw], r2
          
      | Parser_syntax.Label (l, t) -> translate_stmt ctx (l::labelset) t
      
      | Parser_syntax.Continue l -> 
        let rv = mk_assign_fresh_e (Literal Empty) in
        let l = match l with
          | None -> ""
          | Some l -> l in
        let label = List.assoc l ctx.label_continue in
        [ Basic (Assignment rv);
          Goto label
        ], rv.assign_left 
      | Parser_syntax.Break l ->
        let rv = mk_assign_fresh_e (Literal Empty) in
        let l = match l with
          | None -> ""
          | Some l -> l in
        let label = List.assoc l ctx.label_break in
        [ Basic (Assignment rv);
          Goto label
        ], rv.assign_left

      (* Next TODO *) 
  	| Parser_syntax.For (e1, e2, e3, e4) ->   
				let r_init_none = fresh_r () in 
				let r_test_none = fresh_r () in
			  let r_incr_none = fresh_r () in  
				let label1 = fresh_r () in
        let continue = fresh_r () in
        let break = fresh_r () in
        let new_ctx = {ctx with
          label_continue = (("", continue) :: (List.map (fun l -> (l, continue)) labelset)) @ ctx.label_continue;
          label_break = (("", break) :: (List.map (fun l -> (l, break)) labelset)) @ ctx.label_break
        } in
				let r1_stmts, _ = match e1 with 
				   | None -> [ ], r_init_none (* Basic (Assignment (mk_assign r_init_none (Expression (Literal (Empty))))) *)
					 | Some e -> translate_exp ctx e in
					
				let r21_stmts, r21 = match e2 with 
				   | None -> [ Basic (Assignment (mk_assign r_test_none (Expression (Literal (Bool (true)))))) ], r_test_none 
					 | Some e -> translate_exp ctx e in
				
				let r22_stmts, r22 = match e2 with
				   | None -> [ ], r_test_none
					 | Some e -> translate_gamma r21 ctx in
		    
				let r23_stmts, r23 = match e2 with
				   | None -> [ ], r_test_none
					 | Some e -> 
						  let r23_stmt, r231 = translate_to_boolean r22 ctx in
							   [ r23_stmt ], r231 in
					
				let r3_stmts, _ = match e3 with 
				   | None -> [ ], r_incr_none (* Basic (Assignment (mk_assign r_incr_none (Expression (Literal (Empty))))) *)
					 | Some e -> translate_exp ctx e in
							
				let r4_stmts, r4 = translate_stmt new_ctx [] e4 in
				
				(* let r1 = mk_assign_fresh_lit (String "banana") in *)
          r1_stmts @  
					[ Label label1 ] @ 
					r21_stmts @ r22_stmts @ r23_stmts @
					[ Sugar (If (equal_bool_expr r23 true,
					  r4_stmts 
						@
						[ Label continue ]
						@
						r3_stmts
						@
					  [ Goto label1 ], 
						[])) ] @
				  [Label break], ret_def
			
			| Parser_syntax.Switch 	(e, xs) -> 
				(* print_string "Started to switch \n";*)
			  let r_test_stmts1, r_test1 = translate_exp ctx e in
				let r_test_stmts2, r_test2 = translate_gamma r_test1 ctx in
				let break = fresh_r () in
				let r_found_a = fresh_r () in
				let r_found_b = fresh_r () in
				let r_banana = fresh_r () in
				let switch_var = fresh_r () in
				let new_ctx = {ctx with
          label_break = ("", break) :: ctx.label_break 
        } in
				begin 
				(* *)
				let acumulator = List.fold_left (fun acumulator elem ->
					match acumulator.default with
					| None ->
						(match elem with 
						| (Parser_syntax.Case e_case, stmt) ->
							{acumulator with	a_cases = acumulator.a_cases @ [(e_case, stmt)] }
					  | (Parser_syntax.DefaultCase, stmt) -> 
							{acumulator with default = (Some stmt) }) 
					| Some _ ->
						(match elem with 
						| (Parser_syntax.Case e_case, stmt) ->
							let new_acumulator = {acumulator with	b_cases = acumulator.b_cases @ [(e_case, stmt)] } in
								new_acumulator 
						|	(Parser_syntax.DefaultCase, stmt) -> raise (PulpInvalid ("Invalid Syntax. One switch with more than one default.")))) 
			  {a_cases = []; b_cases = []; default = None } xs in	
				(* *)
				let a_stmts = List.map (fun (e_case, stmt) ->  
					let r_case_stmts1, r_case1 = translate_exp new_ctx e_case in
					let r_case_stmts2, r_case2 = translate_gamma r_case1 new_ctx in
					let r_case_stmt3, r_case3 = translate_strict_equality_comparison r_case2 r_test2 in
					let r_case_stmts4, r_stmt = translate_stmt new_ctx [] stmt in 
						[ Basic (Assignment (mk_assign r_banana (Expression (Literal (String "entrei num case!")))));
							Sugar (If (equal_bool_expr r_found_a false, 
							r_case_stmts1 @
							r_case_stmts2 @
							[ r_case_stmt3;
							  Basic (Assignment (mk_assign r_banana (Expression (Literal (String "avaliei a guarda do case")))));
								Sugar (If (equal_bool_expr r_case3 true, 
									[ Basic (Assignment (mk_assign r_found_a  (Expression (Literal (Bool true))))) ] @							 
				      		r_case_stmts4 @
									[ Basic (Assignment (mk_assign switch_var (Expression (Var r_stmt)))) ],
									[]))], 
							[  Basic (Assignment (mk_assign r_banana (Expression (Literal (String "fall through is starting"))))) ] @
							r_case_stmts4)) ]) acumulator.a_cases in 
			  (* *)
			  let b_stmts = List.map (fun (e_case, stmt) ->  
					let r_case_stmts1, r_case1 = translate_exp new_ctx e_case in
					let r_case_stmts2, r_case2 = translate_gamma r_case1 new_ctx in
					let r_case_stmt3, r_case3 = translate_strict_equality_comparison r_case2 r_test2 in
					let r_case_stmts4, r_stmt = translate_stmt new_ctx [] stmt in 
						[ Basic (Assignment (mk_assign r_banana (Expression (Literal (String "entrei num case!")))));
							Sugar (If (equal_bool_expr r_found_b false, 
							r_case_stmts1 @
							r_case_stmts2 @
							[ r_case_stmt3;
							  Basic (Assignment (mk_assign r_banana (Expression (Literal (String "avaliei a guarda do case")))));
								Sugar (If (equal_bool_expr r_case3 true, 
									[ Basic (Assignment (mk_assign r_found_b  (Expression (Literal (Bool true))))) ] @							 
				      		r_case_stmts4 @
									[ Basic (Assignment (mk_assign switch_var (Expression (Var r_stmt)))) ],
									[]))], 
							[  Basic (Assignment (mk_assign r_banana (Expression (Literal (String "fall through is starting"))))) ] @
							r_case_stmts4 )) ]) acumulator.b_cases in
				(* *)
				let simple_b_stmts = List.map (fun (e_case, stmt) ->
					let compiled_stmts, r_stmt = translate_stmt new_ctx [] stmt in
					compiled_stmts @
					[ Basic (Assignment (mk_assign switch_var (Expression (Var r_stmt)))) ]) acumulator.b_cases in 
				(* *)
				let default_stmts = 
					(match acumulator.default with 
					| None -> []
					| Some stmt ->
						let compiled_default_stmts, r_default = translate_stmt new_ctx [] stmt in
							[ Sugar (If (equal_bool_expr r_found_b false,
									compiled_default_stmts @
									[ Basic (Assignment (mk_assign switch_var (Expression (Var r_default)))) ] @
									List.flatten simple_b_stmts, 
									[]))]) in
				(* *)						
			  (* print_string "stop switching now \n"; *)
				[  Basic (Assignment (mk_assign r_banana (Expression (Literal (String "entrei no switch"))))) ] @ 
				r_test_stmts1 @ 
			  r_test_stmts2 @ 
				[ Basic (Assignment (mk_assign r_banana (Expression (Literal (String "avaliei a guarda"))))) ] @
				[ Basic (Assignment (mk_assign r_found_a (Expression (Literal (Bool false))))) ] @
				List.flatten a_stmts @
				[ Basic (Assignment (mk_assign r_found_b (Expression (Literal (Bool false))))) ] @
				[ Sugar (If (equal_bool_expr r_found_a false,
							List.flatten b_stmts, 
							[])); 
					Sugar (If (equal_bool_expr r_found_b false,
							default_stmts, 
							[])); 
					Label break ], ret_def
		  end
      (* I am not considering those *)  
      
      | Parser_syntax.ForIn _ -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:12.6.4 The for-in Statement.")))
      | Parser_syntax.With _ -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:12.10 With Statemenet.")))
      | Parser_syntax.Debugger -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:12.15 The debugger Statement.")))

let builtin_call_boolean_call () =
  let v = fresh_r () in
  let ctx = create_ctx [] in
  let stmt, r1 = translate_to_boolean v ctx in
  let body = to_ivl_goto (* TODO translation level *)
    [ Sugar (If (equal_empty_expr v,
       [ Basic (Assignment (mk_assign r1 (Expression (Literal (Bool false)))))],
       [stmt]));
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var r1))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block (string_of_builtin_function Boolean_Call) body [rthis; rscope; v] ctx
  
let builtin_call_boolean_construct () =
  let v = fresh_r () in
  let ctx = create_ctx [] in
  let new_obj = mk_assign_fresh Obj in
  let stmt, r1 = translate_to_boolean v ctx in
  let body = to_ivl_goto (* TODO translation level *)
    [ Basic (Assignment new_obj);
      add_proto_value new_obj.assign_left Lbp;
      Basic (Mutation (mk_mutation (Var new_obj.assign_left) (literal_builtin_field FClass) (Literal (String "Boolean"))));
      Sugar (If (equal_empty_expr v,
       [ Basic (Assignment (mk_assign r1 (Expression (Literal (Bool false)))))],
       [stmt]));
      Basic (Mutation (mk_mutation (Var new_obj.assign_left) (literal_builtin_field FPrimitiveValue) (Var r1)));
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var new_obj.assign_left))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block (string_of_builtin_function Boolean_Construct) body [rthis; rscope; v] ctx
  
let lbp_common ctx =
  let b = fresh_r () in
  let assign_b e = Basic (Assignment (mk_assign b (Expression e))) in  
  let class_lookup = mk_assign_fresh (Lookup (Var rthis, literal_builtin_field FClass)) in
  let prim_value = mk_assign_fresh (Lookup (Var rthis, literal_builtin_field FPrimitiveValue)) in
  Sugar (If (type_of_var rthis BooleanType,
        [ assign_b (Var rthis)],
        [ Sugar (If (type_of_var rthis (ObjectType None),
            [ 
              Basic (Assignment class_lookup);
              Sugar (If (equal_string_expr class_lookup.assign_left "Boolean",
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
  let body = to_ivl_goto (* TODO translation level *)
    [ stmt;
      Sugar (If (equal_bool_expr b true,
        [assign_rv rv (Literal (String "true"))],
        [assign_rv rv (Literal (String "false"))]));
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var rv))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block (string_of_builtin_function Boolean_Prototype_toString) body [rthis; rscope] ctx
  
let builtin_lbp_valueOf () =
  let ctx = create_ctx [] in
  let stmt, b = lbp_common ctx in
  let body = to_ivl_goto (* TODO translation level *)
    [ stmt;
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var b))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block (string_of_builtin_function Boolean_Prototype_valueOf) body [rthis; rscope] ctx
  
let builtin_lop_toString () =
  let ctx = create_ctx [] in
  let rv = fresh_r () in
  let assign_rv e = Basic (Assignment (mk_assign rv (Expression e))) in  
  let to_object, r1 = translate_to_object rthis ctx in
  let class_lookup = mk_assign_fresh (Lookup (Var r1, literal_builtin_field FClass)) in
  let body = to_ivl_goto (* TODO translation level *)
    [ Sugar (If (equal_undef_expr rthis,
        [ assign_rv (Literal (String "[object Undefined]"))],
        [ Sugar (If (equal_null_expr rthis,
            [ assign_rv (Literal (String "[object Null]"))],
            [ to_object;
              Basic (Assignment class_lookup);
              assign_rv (concat_exprs (concat_exprs (Literal (String "[object ")) (Var class_lookup.assign_left)) (Literal (String "]")));
              ]))
        ]));
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var rv))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block (string_of_builtin_function Object_Prototype_toString) body [rthis; rscope] ctx
  
let builtin_lop_valueOf () =
  let ctx = create_ctx [] in
  let to_object, r1 = translate_to_object rthis ctx in
  let body = to_ivl_goto (* TODO translation level *)
    [ to_object;
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var r1))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block (string_of_builtin_function Object_Prototype_valueOf) body [rthis; rscope] ctx
  
let builtin_object_construct () =
  let v = fresh_r () in
  let ctx = create_ctx [] in
  let rv = fresh_r () in
  let assign_rv e = Basic (Assignment (mk_assign rv (Expression e))) in  
  let stmt, r1 = translate_to_object v ctx in
  let new_obj = mk_assign_fresh Obj in
  let body = to_ivl_goto (* TODO translation level *)
    [ Sugar (If (type_of_var v (ObjectType None),
        [assign_rv (Var v)],
        [ Sugar (If (istypeof_prim_expr v,
            [ stmt; 
              assign_rv (Var r1)
            ],
            [ Basic (Assignment new_obj);
              add_proto_value new_obj.assign_left Lop;
              Basic (Mutation (mk_mutation (Var new_obj.assign_left) (literal_builtin_field FClass) (Literal (String "Object"))));
              assign_rv (Var new_obj.assign_left)
            ]))
        ]));
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var rv))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block (string_of_builtin_function Object_Construct) body [rthis; rscope; v] ctx
  
let builtin_object_call () =
  let v = fresh_r () in
  let ctx = create_ctx [] in
  let rv = fresh_r () in
  let assign_rv e = Basic (Assignment (mk_assign rv (Expression e))) in  
  let stmt, r1 = translate_to_object v ctx in
  let new_obj = mk_assign_fresh Obj in
  let body = to_ivl_goto (* TODO translation level *)
    [ Sugar (If (or_expr 
                   (equal_empty_expr v)
                   (or_expr (equal_undef_expr v) (equal_null_expr v)),
        [ Basic (Assignment new_obj); (* TODO to make this a function for Object(), new Object(), Object literal *)
          add_proto_value new_obj.assign_left Lop;
          Basic (Mutation (mk_mutation (Var new_obj.assign_left) (literal_builtin_field FClass) (Literal (String "Object"))));
          assign_rv (Var new_obj.assign_left)
        ],
        [ stmt; assign_rv (Var r1)]));
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var rv))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block (string_of_builtin_function Object_Call) body [rthis; rscope; v] ctx
  
let builtin_object_get_prototype_of () =
  let v = fresh_r () in
  let ctx = create_ctx [] in
  let body = to_ivl_goto (* TODO translation level *)
    [ Sugar (If (type_of_var v (ObjectType None),
        [ Basic (Assignment (mk_assign ctx.return_var (Lookup (Var v, literal_builtin_field FProto))))],
        translate_error_throw Ltep ctx.throw_var ctx.label_throw));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block (string_of_builtin_function Object_getPrototypeOf) body [rthis; rscope; v] ctx
  
let builtin_lop_is_prototype_of () =
  let v = fresh_r () in
  let ctx = create_ctx [] in
  let to_obj_stmt, o = translate_to_object rthis ctx in
  let proto = mk_assign_fresh (Lookup (Var v, literal_builtin_field FProto)) in
  let proto_o = mk_assign_fresh (ProtoO (Var proto.assign_left, Var o)) in
  let body = to_ivl_goto (* TODO translation level *)
    [ Sugar (If (type_of_var v (ObjectType None), 
	      [ to_obj_stmt;
          Basic (Assignment proto);
	        Basic (Assignment proto_o);
	        Basic (Assignment (mk_assign ctx.return_var (Expression (Var proto_o.assign_left))))
	      ],
	      [Basic (Assignment (mk_assign ctx.return_var (Expression (Literal (Bool false)))))]));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block (string_of_builtin_function Object_Prototype_isPrototypeOf) body [rthis; rscope; v] ctx
  
let builtin_lfp_call () = 
  let ctx = create_ctx [] in
  let body = to_ivl_goto (* TODO translation level *)
    ([ 
      Basic (Assignment (mk_assign ctx.return_var (Expression (Literal Undefined))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ]) in    
  make_function_block (string_of_builtin_function Function_Call) body [rthis; rscope] ctx

let builtin_call_number_call () =
  let v = fresh_r () in
  let ctx = create_ctx [] in
  let stmts, r1 = translate_to_number v ctx in 
  let body = to_ivl_goto (* TODO translation level *)
    ([ 
      Sugar (If (equal_empty_expr v,
        [ Basic (Assignment (mk_assign ctx.return_var (Expression (Literal (Num 0.)))))],
        stmts @ 
        [ Basic (Assignment (mk_assign ctx.return_var (Expression (Var r1))))]));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ]) in    
  make_function_block (string_of_builtin_function Number_Call) body [rthis; rscope; v] ctx
  
let builtin_call_number_construct () =
  let v = fresh_r () in
  let ctx = create_ctx [] in
  let new_obj = mk_assign_fresh Obj in
  let stmts, r1 = translate_to_number v ctx in
  let body = to_ivl_goto (* TODO translation level *)
    ([ Basic (Assignment new_obj);
       add_proto_value new_obj.assign_left Lnp;
       Basic (Mutation (mk_mutation (Var new_obj.assign_left) (literal_builtin_field FClass) (Literal (String "Number"))));
       Sugar (If (equal_empty_expr v,
         [ Basic (Assignment (mk_assign r1 (Expression (Literal (Num 0.)))))],
         stmts));
       Basic (Mutation (mk_mutation (Var new_obj.assign_left) (literal_builtin_field FPrimitiveValue) (Var r1)));
       Basic (Assignment (mk_assign ctx.return_var (Expression (Var new_obj.assign_left))));
       Goto ctx.label_return; 
       Label ctx.label_return; 
       Label ctx.label_throw
     ]) in    
  make_function_block (string_of_builtin_function Number_Construct) body [rthis; rscope; v] ctx
  
let lnp_common ctx =
  let b = fresh_r () in
  let assign_b e = Basic (Assignment (mk_assign b (Expression e))) in  
  let class_lookup = mk_assign_fresh (Lookup (Var rthis, literal_builtin_field FClass)) in
  let prim_value = mk_assign_fresh (Lookup (Var rthis, literal_builtin_field FPrimitiveValue)) in
  Sugar (If (type_of_var rthis NumberType,
        [ assign_b (Var rthis)],
        [ Sugar (If (type_of_var rthis (ObjectType None),
            [ 
              Basic (Assignment class_lookup);
              Sugar (If (equal_string_expr class_lookup.assign_left "Number",
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
  let stmt, b = lbp_common ctx in
  let body = to_ivl_goto (* TODO translation level *)
    [ stmt;
      assign_rv rv (UnaryOp (ToStringOp, Var b));
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var rv))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block (string_of_builtin_function Number_Prototype_toString) body [rthis; rscope] ctx
    
let builtin_lnp_valueOf () =
  let ctx = create_ctx [] in
  let stmt, b = lnp_common ctx in
  let body = to_ivl_goto (* TODO translation level *)
    [ stmt;
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var b))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ] in    
  make_function_block (string_of_builtin_function Number_Prototype_valueOf) body [rthis; rscope] ctx
  
let builtin_global_is_nan () =
  let n = fresh_r () in
  let ctx = create_ctx [] in
  let stmts, r1 = translate_to_number n ctx in 
  let body = to_ivl_goto (* TODO translation level *)
    (stmts @
    [ Sugar (If (equal_num_expr r1 nan,
       [ Basic (Assignment (mk_assign ctx.return_var (Expression (Literal (Bool true)))))],
       [ Basic (Assignment (mk_assign ctx.return_var (Expression (Literal (Bool false)))))]
      ));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ]) in    
  make_function_block (string_of_builtin_function Global_isNaN) body [rthis; rscope; n] ctx
  
let builtin_global_is_finite () =
  let n = fresh_r () in
  let ctx = create_ctx [] in
  let stmts, r1 = translate_to_number n ctx in 
  let body = to_ivl_goto (* TODO translation level *)
    (stmts @
    [ Sugar (If (or_expr 
                  (equal_num_expr r1 nan)
                  (or_expr 
                    (equal_num_expr r1 infinity) 
                    (equal_num_expr r1 neg_infinity)),
       [ Basic (Assignment (mk_assign ctx.return_var (Expression (Literal (Bool false)))))],
       [ Basic (Assignment (mk_assign ctx.return_var (Expression (Literal (Bool true)))))]
      ));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ]) in    
  make_function_block (string_of_builtin_function Global_isFinite) body [rthis; rscope; n] ctx
  
let builtin_call_string_call () =
  let v = fresh_r () in
  let ctx = create_ctx [] in
  let stmts, r1 = translate_to_string v ctx in 
  let body = to_ivl_goto (* TODO translation level *)
   [ Sugar (If (equal_empty_expr v,
       [ Basic (Assignment (mk_assign r1 (Expression (Literal (String "")))))],
       stmts));
     Basic (Assignment (mk_assign ctx.return_var (Expression (Var r1))));
     Goto ctx.label_return; 
     Label ctx.label_return; 
     Label ctx.label_throw
    ] in    
  make_function_block (string_of_builtin_function String_Call) body [rthis; rscope; v] ctx
  
let builtin_call_string_construct () =
  let v = fresh_r () in
  let ctx = create_ctx [] in
  let new_obj = mk_assign_fresh Obj in
  let stmts, r1 = translate_to_string v ctx in 
  let body = to_ivl_goto (* TODO translation level *)
    ([ Basic (Assignment new_obj);
      add_proto_value new_obj.assign_left Lsp;
      Basic (Mutation (mk_mutation (Var new_obj.assign_left) (literal_builtin_field FClass) (Literal (String "String")))); 
      Sugar (If (equal_empty_expr v,
       [ Basic (Assignment (mk_assign r1 (Expression (Literal (String "")))))],
       stmts));
      Basic (Mutation (mk_mutation (Var new_obj.assign_left) (literal_builtin_field FPrimitiveValue) (Var r1)));
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var new_obj.assign_left))));
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ]) in    
  make_function_block (string_of_builtin_function String_Construct) body [rthis; rscope; v] ctx
    
let builtin_lsp_toString_valueOf () =
  let ctx = create_ctx [] in
  let b = fresh_r () in
  let assign_b e = Basic (Assignment (mk_assign b (Expression e))) in  
  let class_lookup = mk_assign_fresh (Lookup (Var rthis, literal_builtin_field FClass)) in
  let prim_value = mk_assign_fresh (Lookup (Var rthis, literal_builtin_field FPrimitiveValue)) in
  let body = to_ivl_goto (* TODO translation level *)
    [ Sugar (If (type_of_var rthis StringType,
        [ assign_b (Var rthis)],
        [ Sugar (If (type_of_var rthis (ObjectType None),
            [ 
              Basic (Assignment class_lookup);
              Sugar (If (equal_string_expr class_lookup.assign_left "String",
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
  make_function_block (string_of_builtin_function String_Prototype_valueOf) body [rthis; rscope] ctx

let exp_to_elem ctx exp : statement list * variable = 
    let r = fresh_r() in
    match exp.Parser_syntax.exp_stx with
      | Parser_syntax.NamedFun (s, name, args, body) -> [Basic (Assignment (mk_assign r (Expression (Literal Empty))))], r (* Things done already *)
      | _ ->  translate_stmt ctx [] exp

let rec exp_to_fb ctx exp : statement list * variable =
  match exp.Parser_syntax.exp_stx with
    | Parser_syntax.Script (_, es) 
    | Parser_syntax.Block (es) -> translate_block es (exp_to_elem ctx) ctx.stmt_return_var
    | _ -> exp_to_elem ctx exp
        
let translate_function fb annots fid main args env named =
  let ctx = create_ctx env in
  
  (*Printf.printf "Env vars in %s: %s" (match named with None -> "None " | Some n -> n)  (String.concat "\n" (List.map (Pulp_Syntax_Print.string_of_ctx_vars) ctx.env_vars));*)
  
  let other_env = match ctx.env_vars, named with
    | current :: others, None -> others
    | current_decl :: others, Some _ ->
      begin match others with
        | [] -> raise (Invalid_argument "Should be a function environment here")
        | current :: others -> current_decl :: others
      end
    | [], _ -> raise (Invalid_argument "Should be a function environment here") in
    
  let init_e = List.map (fun env -> 
     Basic (Assignment (mk_assign (function_scope_name env.func_id) (Lookup (Var rscope, Literal (String env.func_id)))))
  ) other_env in
  
  let current_scope_var = function_scope_name fid in
  
  let current_scope_stmts = 
    if (fid = main_fun_id) then
      [Basic (Assignment (mk_assign current_scope_var (Expression (Literal (LLoc Lg)))));
       add_proto_value current_scope_var Lop;
       Basic (Mutation (mk_mutation (Literal (LLoc Lg)) (Literal (String "undefined")) (Literal Undefined)))]
  else 
       [Basic (Assignment (mk_assign current_scope_var Obj));
        add_proto_null current_scope_var] in
        
  let init_vars = Utils.flat_map (fun v ->
      [
        Basic (Mutation (mk_mutation (Var current_scope_var) (Literal (String v)) (Var v)))
      ]
    ) args in
    
  (* Creating function declarations *)
  let func_decls_used_vars = List.map (fun f ->
     match f.Parser_syntax.exp_stx with
      | Parser_syntax.NamedFun (_, name, params, body) -> 
        let stmts, lvar = translate_function_expression f params ctx None in
        stmts @
	      [
	        Basic (Mutation (mk_mutation (Var current_scope_var) (Literal (String name)) (Var lvar)))
	      ], name
      | _ ->  [], "" (* TODO *)   
    ) (func_decls_in_exp fb) in
    
   let func_decls, used_vars = List.split func_decls_used_vars in
   let used_vars = used_vars @ args in
    
  (* Assigning undefined to var declarations *)
  let decl_vars = Utils.flat_map (fun v ->
      [
        Basic (Mutation (mk_mutation (Var current_scope_var) (Literal (String v)) (Literal Undefined)))
      ]
    ) (List.filter (fun v -> not (List.mem v used_vars)) (var_decls fb)) in
    
  let pulp_fb, lvar = exp_to_fb ctx fb in
  
  let end_stmts =
    if (fid = main) then
      [ Sugar (If (equal_empty_expr lvar,
        [Basic (Assignment (mk_assign ctx.return_var (Expression (Literal Undefined))))],
        [Basic (Assignment (mk_assign ctx.return_var (Expression (Var lvar))))]))
      ]
    else
      [Basic (Assignment (mk_assign ctx.return_var (Expression (Literal Undefined))))] in
    
  let pulpe = 
		[ Basic (Assignment (mk_assign ctx.stmt_return_var (Expression (Literal Empty))))] @
    init_e @ 
    current_scope_stmts @  
    init_vars @ 
    (List.flatten func_decls) @
    decl_vars @ 
    pulp_fb @
    end_stmts @
    [
      Goto ctx.label_return; 
      Label ctx.label_return; 
      Label ctx.label_throw
    ]
  in
  
  let spec = Pulp_Formula_Parser_Utils.get_function_spec annots in
  
  make_function_block_with_spec fid pulpe (rthis :: (rscope :: args)) ctx spec

let translate_function_syntax level id e named env main =
  let pulpe = 
    match e.Parser_syntax.exp_stx with
      | Parser_syntax.AnnonymousFun (_, args, fb) -> translate_function fb e.Parser_syntax.exp_annot id main args env None
      | Parser_syntax.NamedFun (_, name, args, fb) -> translate_function fb e.Parser_syntax.exp_annot id main args env named
      | Parser_syntax.Script (_, es) -> translate_function e e.Parser_syntax.exp_annot main main [] env None
      | _ -> raise (Invalid_argument "Should be a function definition here") in
  match level with
    | IVL_buitin_functions -> pulpe
    | IVL_conditionals -> {pulpe with func_body = unfold_spec_functions pulpe.func_body}
    | IVL_goto -> {pulpe with func_body = to_ivl_goto pulpe.func_body}

let exp_to_pulp_no_builtin level e main ctx_vars = 
  let context = AllFunctions.empty in
  let e = add_codenames main e in
  let all_functions = get_all_functions_with_env_in_fb [] e main in
    
  List.fold_left (fun c (fexpr, fnamed, fenv) -> 
    let fid = get_codename fexpr in
    let fb = translate_function_syntax level fid fexpr fnamed  (fenv @ ctx_vars) main in
    AllFunctions.add fid fb c
   ) context all_functions
  

let exp_to_pulp level e main ctx_vars =
  let context = exp_to_pulp_no_builtin level e main ctx_vars in
  
  let context = AllFunctions.add (string_of_builtin_function Boolean_Call) (builtin_call_boolean_call()) context in
  let context = AllFunctions.add (string_of_builtin_function Boolean_Construct) (builtin_call_boolean_construct()) context in
  let context = AllFunctions.add (string_of_builtin_function Boolean_Prototype_toString) (builtin_lbp_toString()) context in
  let context = AllFunctions.add (string_of_builtin_function Boolean_Prototype_valueOf) (builtin_lbp_valueOf()) context in
  let context = AllFunctions.add (string_of_builtin_function Object_Prototype_toString) (builtin_lop_toString()) context in
  let context = AllFunctions.add (string_of_builtin_function Object_Prototype_valueOf) (builtin_lop_valueOf()) context in
  let context = AllFunctions.add (string_of_builtin_function Object_Prototype_isPrototypeOf) (builtin_lop_is_prototype_of()) context in 
  let context = AllFunctions.add (string_of_builtin_function Object_Construct) (builtin_object_construct()) context in
  let context = AllFunctions.add (string_of_builtin_function Object_Call) (builtin_object_call()) context in
  let context = AllFunctions.add (string_of_builtin_function Object_getPrototypeOf) (builtin_object_get_prototype_of()) context in  
  let context = AllFunctions.add (string_of_builtin_function Number_Call) (builtin_call_number_call()) context in
  let context = AllFunctions.add (string_of_builtin_function Number_Construct) (builtin_call_number_construct()) context in
  let context = AllFunctions.add (string_of_builtin_function Number_Prototype_toString) (builtin_lnp_toString()) context in
  let context = AllFunctions.add (string_of_builtin_function Number_Prototype_valueOf) (builtin_lnp_valueOf()) context in
  let context = AllFunctions.add (string_of_builtin_function String_Call) (builtin_call_string_call()) context in
  let context = AllFunctions.add (string_of_builtin_function String_Construct) (builtin_call_string_construct()) context in
  let context = AllFunctions.add (string_of_builtin_function String_Prototype_toString) (builtin_lsp_toString_valueOf()) context in
  let context = AllFunctions.add (string_of_builtin_function String_Prototype_valueOf) (builtin_lsp_toString_valueOf()) context in
  let context = AllFunctions.add (string_of_builtin_function Function_Prototype_Call) (builtin_lfp_call()) context in
  let context = AllFunctions.add (string_of_builtin_function Global_isNaN) (builtin_global_is_nan()) context in
  let context = AllFunctions.add (string_of_builtin_function Global_isFinite) (builtin_global_is_finite()) context in
  
  context
