open Batteries
open Pulp_Syntax
open Pulp_Syntax_Utils
open Pulp_Syntax_Print

exception PulpNotImplemented of string
exception PulpInvalid of string

type translation_level =
  | IVL_buitin_functions
  | IVL_conditionals
  | IVL_goto
 
  
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
let is_obj_var v = IsTypeOf (Var v, (ObjectType None))

let or_expr e1 e2 = BinOp (e1, Boolean Or, e2)
let and_expr e1 e2 = BinOp (e1, Boolean And, e2)
let not_expr e1 = UnaryOp (Not, e1)
let equal_exprs e1 e2 = BinOp (e1, Comparison Equal, e2)
let equal_expr v e2 = equal_exprs (Var v) e2

let lessthan_exprs e1 e2 = or_expr 
    (BinOp (e1, Comparison LessThan, e2)) 
    (BinOp (e1, Comparison Equal, e2))
 
let type_of_var v t = lessthan_exprs (TypeOf (Var v)) (Literal (Type t))
let type_of_oref_var ref = type_of_var ref (ReferenceType (Some MemberReference))
let type_of_vref_var ref = type_of_var ref (ReferenceType (Some VariableReference))
let type_of_ref_var ref = type_of_var ref (ReferenceType None)
  
let istypeof_prim_expr v =
  or_expr 
  (IsTypeOf (Var v, BooleanType))
  (or_expr 
    (IsTypeOf (Var v, NumberType))
    (IsTypeOf (Var v, StringType)))
    
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

(* What about not a number? *)
let is_false_expr v =
  or_expr
  (equal_bool_expr v false)
	  (or_expr
	  (equal_int_expr v 0)
	  (or_expr
		  (equal_string_expr v "")
	    (or_expr
			  (equal_undef_expr v)
			  (equal_null_expr v))))
      
let is_true_expr v =  
  and_expr
  (not_expr (equal_bool_expr v false)) 
	  (and_expr
	  (not_expr (equal_int_expr v 0))
	  (and_expr
	    (not_expr (equal_string_expr v ""))
	    (and_expr
	          (not_expr (equal_undef_expr v))
	          (not_expr (equal_null_expr v)))))

(* Assignment *)
let mk_assign var exp = { 
    assign_left = var; 
    assign_right = exp
  }

(* Assignment to a fresh variable *)
let mk_assign_fresh exp = mk_assign (fresh_r ()) exp
  
let mk_assign_fresh_e e = mk_assign_fresh (Expression e)
let mk_assign_fresh_lit lit = mk_assign_fresh_e (Literal lit)


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
      | Parser_syntax.Plus -> Plus
      | Parser_syntax.Minus -> Minus
      | Parser_syntax.Times -> Times
      | Parser_syntax.Div -> Div
      | Parser_syntax.Mod -> Mod
      | Parser_syntax.Ursh -> raise (PulpNotImplemented ((Pretty_print.string_of_arith_op op ^ " REF:11.7.3 The Unsigned Right Shift Operator.")))
      | Parser_syntax.Lsh -> raise (PulpNotImplemented ((Pretty_print.string_of_arith_op op ^ " REF:11.7.1 The Left Shift Operator.")))
      | Parser_syntax.Rsh -> raise (PulpNotImplemented ((Pretty_print.string_of_arith_op op ^ " REF:11.7.2 The Signed Right Shift Operator.")))
      | Parser_syntax.Bitand -> raise (PulpNotImplemented ((Pretty_print.string_of_arith_op op ^ " REF:11.10 Binary Bitwise Operators.And.")))
      | Parser_syntax.Bitor -> raise (PulpNotImplemented ((Pretty_print.string_of_arith_op op ^ " REF:11.10 Binary Bitwise Operators.Or.")))
      | Parser_syntax.Bitxor -> raise (PulpNotImplemented ((Pretty_print.string_of_arith_op op ^ " REF:11.10 Binary Bitwise Operators.Xor.")))
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
    | Parser_syntax.Arith op -> Arith (tr_arith_op op)
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
  
let translate_strict_equality_comparison x y = 
  let rv = fresh_r() in
  let rv_true = Basic (Assignment (mk_assign rv (Expression (Literal (Bool true))))) in
  let rv_false = Basic (Assignment (mk_assign rv (Expression (Literal (Bool false))))) in
  
  let if1 = Sugar (If (equal_exprs (TypeOf (Var x)) (TypeOf (Var y)), 
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
              Sugar (If (equal_expr x (Literal (String "NaN")), (* TODO *)
              [rv_false],
              [
                Sugar (If (equal_expr y (Literal (String "NaN")), (* TODO *)
                [rv_false],
                [
                  Sugar (If (equal_expr x (Var y), 
                  [rv_true], 
                  [
                    Sugar (If (and_expr (equal_expr x (Literal (String "+0"))) (equal_expr x (Literal (String "-0"))),
                    [rv_true],
                    [
                      Sugar (If (and_expr (equal_expr x (Literal (String "-0"))) (equal_expr x (Literal (String "+0"))),
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
    ],
    [ rv_false ]))
  
  in if1, rv
  
let translate_error_throw error throw_var throw_label =
  let r1 = mk_assign_fresh Obj in
  [
    Basic (Assignment r1); 
    add_proto_value r1.assign_left error; 
    Basic (Assignment (mk_assign throw_var (Expression (Var r1.assign_left)))); 
    Goto throw_label
  ]
  
let translate_put_value v1 v2 throw_var throw_label =
  let gotothrow = translate_error_throw LRError throw_var throw_label in
  let base = mk_assign_fresh_e (Base (Var v1)) in
  let main = Sugar (If (is_ref_expr v1,
    [
      Basic (Assignment base);
      Sugar (If (equal_undef_expr base.assign_left, 
        gotothrow, 
        [
          Sugar (If (istypeof_prim_expr base.assign_left, 
            translate_error_throw LTError throw_var throw_label, 
            [Basic (Mutation (mk_mutation (Var base.assign_left) (Field (Var v1)) (Var v2)))]))
        ]))
    ],
    gotothrow))
  in
  main
  
let translate_gamma r ctx =
  let rv = fresh_r () in
  let base = mk_assign_fresh_e (Base (Var r)) in
  let field = mk_assign_fresh_e (Field (Var r)) in
  let assign_rv_lookup = mk_assign rv (Lookup (Var base.assign_left, Var field.assign_left)) in
  let assign_pi_1 = mk_assign_fresh (ProtoF (Var base.assign_left, Var field.assign_left)) in  
  let assign_pi_2 = mk_assign_fresh (ProtoF (Var base.assign_left, Var field.assign_left)) in  
  let main = Sugar (If (is_ref_expr r,
    [
      Basic (Assignment base);
      Sugar (If (equal_undef_expr base.assign_left,
        translate_error_throw LRError ctx.throw_var ctx.label_throw,
        [
          Sugar (If (istypeof_prim_expr base.assign_left,
            translate_error_throw (LNotImplemented GetValuePrim) ctx.throw_var ctx.label_throw,
            [
              Basic (Assignment field);
              Sugar (If (is_vref_expr r,
                [ 
                  Sugar (If (equal_loc_expr base.assign_left Lg,
                  [
                    Basic (Assignment assign_pi_1);
                    Sugar (If (equal_empty_expr assign_pi_1.assign_left,
                      translate_error_throw LRError ctx.throw_var ctx.label_throw,
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
  let gotothrow = translate_error_throw LTError ctx.throw_var ctx.label_throw in 
  [
    Sugar (If (equal_null_expr r, gotothrow, [])); 
    Sugar (If (equal_undef_expr r, gotothrow, [])); 
    Basic (Assignment (mk_assign rv (Expression (Literal Empty))))
  ], rv
  
let translate_call_construct_start f e1 e2s ctx =
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
    let gotothrow = translate_error_throw LTError ctx.throw_var ctx.label_throw in
    let hasfield = mk_assign_fresh (HasField (Var r2, literal_builtin_field FId)) in
    (
      r1_stmts @ 
      r2_stmts @ 
      arg_stmts @ 
      [
        Sugar (If (is_obj_var r2, [], gotothrow)); 
        Basic (Assignment hasfield); 
        Sugar (If (equal_bool_expr hasfield.assign_left false, gotothrow, []))
      ], r1, r2, arg_values)
    
let translate_call r2 vthis arg_values ctx =
    let fid = mk_assign_fresh (Lookup (Var r2, literal_builtin_field FId)) in
	let fscope = mk_assign_fresh (Lookup (Var r2, literal_builtin_field FScope)) in
    let excep_label = "call_excep." ^ fresh_r () in
    let exit_label = fresh_r () in
    let rv = fresh_r() in
         
	let call = mk_assign rv (Call (mk_call 
	  (Var fid.assign_left) 
	  (Var fscope.assign_left) 
	  (Var vthis) 
      arg_values
      excep_label
    )) in
        [
          Basic (Assignment fid); 
          Basic (Assignment fscope); 
          Basic (Assignment call);
          Goto exit_label;
          Label excep_label;
          Basic (Assignment (mk_assign ctx.throw_var (Expression (Var call.assign_left))));
          Goto ctx.label_throw;
          Label exit_label;
        ], rv
    
let translate_regular_bin_op f op e1 e2 ctx =
  let r1_stmts, r1 = f e1 in
  let r2_stmts, r2 = translate_gamma r1 ctx in
  let r3_stmts, r3 = f e2 in
  let r4_stmts, r4 = translate_gamma r3 ctx in
  let r5 = mk_assign_fresh_e (BinOp (Var r2, tr_bin_op op, Var r4)) in
    r1_stmts @ 
    r2_stmts @ 
    r3_stmts @ 
    r4_stmts @ 
    [Basic (Assignment r5)],
    r5.assign_left
    
let translate_not_equal_bin_op f op e1 e2 ctx =
  let r1_stmts, r1 = translate_regular_bin_op f (Parser_syntax.Comparison (Parser_syntax.Equal)) e1 e2 ctx in
  let r2 = mk_assign_fresh (Expression (UnaryOp (Not, (Var r1)))) in
    r1_stmts @ 
    [
     Basic (Assignment r2)
    ], r2.assign_left
    
let translate_abstract_relation x y leftfirst =
  (* TODO Type Conversions *)
  let r6 = mk_assign_fresh_e (BinOp (Var x, Comparison LessThan, Var y)) in
  [Basic (Assignment r6)], r6.assign_left
  
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
  
  let r1_stmts, r1 = translate_call obj vthis args ctx in
  [ Sugar (If (type_of_var obj (ObjectType (Some Builtin)),
    [ Basic (Assignment fid);
      Sugar (If (equal_loc_expr obj LEval,
        [Sugar (If ((*equal_exprs (TypeOf first_argument) (Literal (Type StringType))*) IsTypeOf (first_argument, StringType),
            [
             Basic (Assignment fscope_eval);
             add_proto_null fscope_eval.assign_left] @
            env_stmts @
            [Basic (Assignment eval_call);
            ],
            [Basic (Assignment (mk_assign rv (Expression first_argument)))]))
        ], [Basic (Assignment builtincall)]));
      Goto exit_label;
      Label excep_label;
      Basic (Assignment (mk_assign ctx.throw_var (Expression (Var rv))));
      Goto ctx.label_throw;
      Label exit_label; 
    ],
    r1_stmts @ [Basic (Assignment (mk_assign rv (Expression (Var r1))))]))
  ], rv
  
let default_value_inner arg m rv exit_label next_label ctx =
  let r1_stmts, r1 = translate_get arg (Literal (String m)) in
  let hasfield = mk_assign_fresh (HasField (Var r1, literal_builtin_field FId)) in
  let fid = mk_assign_fresh (Lookup (Var r1, literal_builtin_field FId)) in
  let r2_stmts, r2 = translate_inner_call r1 r1 [] ctx in
  let assign_rv_var var = [Basic (Assignment (mk_assign rv (Expression (Var var))))] in
  r1_stmts @                          
  [ Basic (Assignment hasfield);
    Sugar (If (equal_bool_expr hasfield.assign_left true, 
    [ Basic (Assignment fid) ] @ 
      r2_stmts @
    [ Sugar (If (is_prim_value r2,
      assign_rv_var r2 @ [Goto exit_label],
      []))
    ],
    [Goto next_label]))
  ]
  
let translate_default_value arg preftype ctx =
  let first, second = 
    (if preftype = (Some StringType) then "toString", "toValue"
                                     else "toValue", "toString") in
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
  translate_error_throw LRError ctx.throw_var ctx.label_throw @
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
  
(* TODO : redo *)
let translate_to_boolean arg ctx =
  let rv = fresh_r () in
  let assign_rv b = [Basic (Assignment (mk_assign rv (Expression (Literal (Bool b)))))] in
  let assign_rv_var var = [Basic (Assignment (mk_assign rv (Expression (Var var))))] in
  Sugar (If (type_of_var arg UndefinedType,
    assign_rv false,
    [ Sugar (If (type_of_var arg NullType,
      assign_rv false,
      [ Sugar (If (type_of_var arg BooleanType,
        assign_rv_var arg,
        [ Sugar (If (type_of_var arg StringType,
          [ Sugar (If (equal_string_expr arg "",
              assign_rv false,
              assign_rv true))
          ],
          [ Sugar (If (type_of_var arg (ObjectType None),
              assign_rv true,
              [ Sugar (If (or_expr 
                            (or_expr (equal_num_expr arg Float.nan) (equal_num_expr arg 0.0)) 
                            (equal_num_expr arg (-0.0)),
                  assign_rv false,
                  assign_rv true))
              ])) (* Must be a number *)
          ]))
        ]))
      ]))
    ])), rv
  
let translate_to_number arg ctx =
  let rv = fresh_r () in
  let assign_rv v = [Basic (Assignment (mk_assign rv (Expression (Literal (Num v)))))] in
  let assign_rv_var var = [Basic (Assignment (mk_assign rv (Expression (Var var))))] in
  Sugar (If (type_of_var arg UndefinedType,
    assign_rv Float.nan, (* TODO *)
    [ Sugar (If (type_of_var arg NullType,
      assign_rv 0.0,
      [ Sugar (If (type_of_var arg BooleanType,
        [ Sugar (If (equal_bool_expr arg true, 
          assign_rv 1.0,
          assign_rv 0.0))
        ],
        [ Sugar (If (type_of_var arg NumberType,
          assign_rv_var arg,
          translate_error_throw (LNotImplemented ToNumber) ctx.throw_var ctx.label_throw))
        ]))
      ]))
    ])), rv
    
let translate_to_string arg ctx =
  let rv = fresh_r () in
  let assign_rv v = [Basic (Assignment (mk_assign rv (Expression (Literal (String v)))))] in
  let assign_rv_var var = [Basic (Assignment (mk_assign rv (Expression (Var var))))] in
  Sugar (If (type_of_var arg UndefinedType,
    assign_rv "undefined", (* TODO *)
    [ Sugar (If (type_of_var arg NullType,
      assign_rv "null",
      [ Sugar (If (type_of_var arg BooleanType,
        [ Sugar (If (equal_bool_expr arg true, 
          assign_rv "true",
          assign_rv "false"))
        ],
        [ Sugar (If (type_of_var arg StringType,
          assign_rv_var arg,
          translate_error_throw (LNotImplemented ToString) ctx.throw_var ctx.label_throw))
        ]))
      ]))
    ])), rv
    
let translate_to_number_bin_op f op e1 e2 ctx =
  let r1_stmts, r1 = f e1 in
  let r2_stmts, r2 = translate_gamma r1 ctx in
  let r3_stmts, r3 = f e2 in
  let r4_stmts, r4 = translate_gamma r3 ctx in
  let r5_stmt, r5 = translate_to_number r2 ctx in
  let r6_stmt, r6 = translate_to_number r4 ctx in 
  let r7 = mk_assign_fresh_e (BinOp (Var r5, tr_bin_op op, Var r6)) in
    r1_stmts @ 
    r2_stmts @ 
    r3_stmts @ 
    r4_stmts @ 
    [ r5_stmt;
      r6_stmt; 
      Basic (Assignment r7)],
    r7.assign_left
  
   
let translate_bin_op_logical f e1 e2 bop ctx =
  (* TODO do conversion for boolean *)
  let op = tr_boolean_op bop in
  let r1_stmts, r1 = f e1 in
  let r2_stmts, r2 = translate_gamma r1 ctx in
  let rv = fresh_r () in
  let r3_stmts, r3 = f e2 in
  let r4_stmts, r4 = translate_gamma r3 ctx in
    r1_stmts @ 
    r2_stmts @ 
    [
      Sugar (If ((if (op = And) then (is_false_expr r2) else (is_true_expr r2)), 
        [Basic (Assignment (mk_assign rv (Expression (Var r2))))], 
	      (r3_stmts) @ 
	      r4_stmts @ 
	      [Basic (Assignment (mk_assign rv (Expression (BinOp (Var r2, Boolean op, Var r4)))))]))
    ], rv
  
let rec to_ivl_goto stmts = 
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

let translate_function_expression exp ctx named =
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
    add_proto_value f_obj.assign_left Lfp;
    Basic (Assignment prototype); 
    add_proto_value prototype.assign_left Lop; 
    Basic (Mutation (mk_mutation (Var f_obj.assign_left) (literal_builtin_field FPrototype) (Var prototype.assign_left)));
    Basic (Assignment scope);
    add_proto_null scope.assign_left
  ] @ 
  decl_stmts @
  env_stmts @ 
  [
    Basic (Mutation (mk_mutation (Var f_obj.assign_left) (literal_builtin_field FId) (Literal (String fid)))); 
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
      translate_error_throw LTError ctx.throw_var ctx.label_throw))
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
  let to_number_stmt, oldvalue = translate_to_number r2 ctx in
  let newvalue = mk_assign_fresh_e (BinOp (Var oldvalue, Arith op, (Literal (Num 1.0)))) in          
    r1_stmts @  
    [Sugar (If (and_expr (is_vref_expr r1)
                  (or_expr 
                  (equal_string_exprs (Field (Var r1)) "arguments") 
                  (equal_string_exprs (Field (Var r1)) "eval")), 
      translate_error_throw LSError ctx.throw_var ctx.label_throw, 
      r2_stmts @  
      [ to_number_stmt;
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
      
      | Parser_syntax.This -> 
        begin 
          let assign = mk_assign_fresh_e (Var rthis) in 
          [Basic (Assignment assign)], assign.assign_left
        end
        
      | Parser_syntax.Var v -> 
        begin 
          let scope = find_var_scope v ctx.env_vars in
          let ref_assign = mk_assign_fresh_e (Ref (scope, Literal (String v) , VariableReference)) in
          [Basic (Assignment ref_assign)], ref_assign.assign_left         
        end
        
      | Parser_syntax.Obj xs ->
        begin
          let r1 = mk_assign_fresh Obj in
          
          let stmts = List.map (fun (prop_name, prop_type, e) ->
            match prop_type with
              | Parser_syntax.PropbodyVal ->
                begin
                  let r2_stmts, r2 = f e in
                  let r3_stmts, r3 = translate_gamma r2 ctx in
                  
                  r2_stmts @ 
                  r3_stmts @ 
                  [Basic (Mutation (mk_mutation (Var r1.assign_left) (Literal (String (Pretty_print.string_of_propname prop_name))) (Var r3)))] 
                   
                end
              | _ -> raise (PulpNotImplemented ("Getters and Setters are not yet implemented REF:11.1.5 Object Initialiser.Get.Set."))
            ) xs in
                           
            [
              Basic (Assignment r1);
              add_proto_value r1.assign_left Lop
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
          let r6 = mk_assign_fresh_e (Ref (Var r2, Var r4, MemberReference)) in
            r1_stmts @ 
            r2_stmts @ 
            r3_stmts @ 
            r4_stmts @ 
            r5_stmts @ 
            [Basic (Assignment r6)], r6.assign_left
            
      | Parser_syntax.New (e1, e2s) ->
        let stmts, r1, r2, arg_values = translate_call_construct_start f e1 e2s ctx in
        let prototype = mk_assign_fresh (Lookup (Var r2, literal_builtin_field FPrototype)) in        
        let vthisproto = fresh_r () in
        let vthis = mk_assign_fresh Obj in
        let if3, call_lvar = translate_call r2 vthis.assign_left arg_values ctx in
        let rv = fresh_r () in  
          stmts @ 
          [
            Basic (Assignment prototype); 
            Sugar (If (is_obj_var prototype.assign_left, 
                [Basic (Assignment (mk_assign vthisproto (Expression (Var prototype.assign_left))))], 
                [Basic (Assignment (mk_assign vthisproto (Expression (Literal (LLoc Lop)))))])); 
            Basic (Assignment vthis);
            add_proto_var vthis.assign_left vthisproto 
          ] @
          if3 @ 
          [  Sugar (If (is_obj_var call_lvar, 
                [Basic (Assignment (mk_assign rv (Expression (Var call_lvar))))], 
                [Basic (Assignment (mk_assign rv (Expression (Var vthis.assign_left))))]))
          ], rv
        
      | Parser_syntax.Call (e1, e2s) ->
        let stmts, r1, r2, arg_values = translate_call_construct_start f e1 e2s ctx in
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
          
      | Parser_syntax.AnnonymousFun _ ->
        translate_function_expression exp ctx None
        
      | Parser_syntax.NamedFun (_, name, _, _) -> 
        translate_function_expression exp ctx (Some name)
          
      | Parser_syntax.Unary_op (op, e) ->
        begin match op with 
          | Parser_syntax.Not ->
            let r1_stmts, r1 = f e in
            let r2_stmts, r2 = translate_gamma r1 ctx in
            let rv = fresh_r () in 
            let if1 = 
              Sugar (If (is_false_expr r2, 
                [
                  Basic (Assignment (mk_assign rv (Expression (Literal (Bool true)))))
                ], 
                [
                  Basic (Assignment (mk_assign rv (Expression (Literal (Bool false)))))
                ])) in
                r1_stmts @
            r2_stmts @
            [if1], rv
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
            let r3_stmt, r3 = translate_to_number r2 ctx in
            r1_stmts @
            r2_stmts @
            [r3_stmt], r3
					| Parser_syntax.Negative -> 
            let r1_stmts, r1 = f e in
            let r2_stmts, r2 = translate_gamma r1 ctx in
            let r3_stmt, r3 = translate_to_number r2 ctx in
            let rv = fresh_r () in
            let assign_rv n = [Basic (Assignment (mk_assign rv (Expression n)))] in
            let negative = mk_assign_fresh_e (UnaryOp (Negative, (Var r3))) in
            r1_stmts @
            r2_stmts @
            [r3_stmt;
             Sugar (If (equal_num_expr r3 Float.nan,
               assign_rv (Literal (Num Float.nan)),
               [Basic (Assignment negative)] @
               assign_rv (Var negative.assign_left)))
            ], negative.assign_left
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
		  | Parser_syntax.Bitnot -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:11.4.8 Bitwise NOT Operator.")))
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
                        translate_error_throw LTError ctx.throw_var ctx.label_throw, 
                        [Basic (Assignment assign_rv_true)]))
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
                  let r5_stmts, r5 = translate_abstract_relation r2 r4 true in
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
                  let r5_stmts, r5 = translate_abstract_relation r4 r2 false in
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
                  let r5_stmts, r5 = translate_abstract_relation r4 r2 false in
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
                  let r5_stmts, r5 = translate_abstract_relation r2 r4 true in
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
                let r5_stmt, r5 = translate_to_string r2 ctx in
                let r6_stmts, r6 = translate_has_property r4 (Var r5) in
                r1_stmts @ 
                r2_stmts @ 
                r3_stmts @ 
                r4_stmts @
                [ Sugar (If (lessthan_exprs (TypeOf (Var r4)) (Literal (Type (ObjectType None))), 
                    [r5_stmt] @ r6_stmts,
                    translate_error_throw LTError ctx.throw_var ctx.label_throw))
                ], r6
			| Parser_syntax.InstanceOf -> 
                let r1_stmts, r1 = f e1 in
                let r2_stmts, r2 = translate_gamma r1 ctx in
                let r3_stmts, r3 = f e2 in
                let r4_stmts, r4 = translate_gamma r3 ctx in
                let hasfield = mk_assign_fresh (HasField (Var r4, literal_builtin_field FId)) in
                let gotothrow = translate_error_throw LTError ctx.throw_var ctx.label_throw in
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
              | Parser_syntax.Plus -> translate_regular_bin_op f op e1 e2 ctx
              | Parser_syntax.Minus
              | Parser_syntax.Times
              | Parser_syntax.Div 
              | Parser_syntax.Mod -> translate_to_number_bin_op f op e1 e2 ctx
						  | Parser_syntax.Ursh -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:11.7.3 The Unsigned Right Shift Operator.")))
						  | Parser_syntax.Lsh -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:11.7.1 The Left Shift Operator.")))
						  | Parser_syntax.Rsh -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:11.7.2 The Signed Right Shift Operator.")))
						  | Parser_syntax.Bitand -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:11.10 Binary Bitwise Operators.And.")))
						  | Parser_syntax.Bitor -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:11.10 Binary Bitwise Operators.Or.")))
						  | Parser_syntax.Bitxor -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:11.10 Binary Bitwise Operators.Xor.")))
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
          let gotothrow = translate_error_throw LRError ctx.throw_var ctx.label_throw in
          
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
        let rv = fresh_r () in     
          r1_stmts @ 
          r2_stmts @ 
          [ 
            Sugar (If (is_true_expr r2, 
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
          let label = fresh_r () in
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
                 [Goto label]))
              ],
		          [ Label label;
                translate_put_value r1 r5.assign_left ctx.throw_var ctx.label_throw
              ]))
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

let translate_block es f =
     let mk_if rval oldrval =
      let retv = fresh_r () in 
        [
          (* DSA *) 
          Sugar (If (equal_empty_expr rval, 
            [
              Basic (Assignment (mk_assign retv (Expression (Var oldrval))))
            ], 
            [
              Basic (Assignment (mk_assign retv (Expression (Var rval))))
            ]))
        ], retv in
     
    let retv = mk_assign_fresh_lit Empty in
    
    List.fold_left (fun (prev_stmts, prev) current -> 
      let r1_stmts, r1 = f current in
      let if_stmts, ifv = mk_if r1 prev in
      (prev_stmts @ r1_stmts @ if_stmts, ifv)) 
    ([Basic (Assignment retv)], retv.assign_left) es

let rec translate_stmt ctx exp : statement list * variable =
  let f = translate_stmt ctx in 
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
        stmts @ gamma_stmts, r2

      | Parser_syntax.AnnonymousFun _
      | Parser_syntax.NamedFun _ -> raise (PulpInvalid ("Expected statement. Actual " ^ (Pretty_print.string_of_exp true exp)))
         (* If a function appears in the middle of a statement, it shall not be interpreted as an expression function, but as a function declaration *)
         (* NOTE in spec p.86 *)
         (* ... It is recommended that ECMAScript implementations either disallow this usage of FunctionDeclaration or issue a warning *)

      (*Statements*)
      | Parser_syntax.Script _ -> raise (PulpInvalid ("Expected Statememnt. Got Script"))
      | Parser_syntax.Block es -> translate_block es f

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
        let rv = fresh_r () in
        let elsebranch = match e3 with
          | Some e3 -> 
            let r4_stmts, r4 = f e3 in
            r4_stmts @ 
            [Basic (Assignment (mk_assign rv (Expression (Var r4))))]
          | None -> [Basic (Assignment (mk_assign rv (Expression (Literal Empty))))] in      
          r1_stmts @ 
          r2_stmts @ 
          [ 
            Sugar (If (is_true_expr r2, 
                r3_stmts @ 
                [Basic (Assignment (mk_assign rv (Expression (Var r3))))], 
                elsebranch))
          ], rv
           
      | Parser_syntax.While (e1, e2) ->
        (* TODO: Update with continue/break *)
        let rv = fresh_r () in
        let assign_rv_empty = Basic (Assignment (mk_assign rv (Expression (Literal Empty)))) in
        let label1 = fresh_r () in
        let r1_stmts, r1 = translate_exp ctx e1 in
        let r2_stmts, r2 = translate_gamma r1 ctx in
        let r3_stmts, r3 = f e2 in
          [
            assign_rv_empty; 
            Label label1
          ] @ 
          r1_stmts @ 
          r2_stmts @ 
          [
            Sugar (If (is_true_expr r2, 
                r3_stmts @ 
                [ 
                  Sugar (If (equal_empty_expr r3, 
                    [], 
                    [Basic (Assignment (mk_assign rv (Expression (Var r3))))])); 
                  Goto label1
                ], 
                
                []))
          ], rv
          
      | Parser_syntax.DoWhile (e1, e2) -> 
        (* TODO: Update with continue/break *)
        let rv = fresh_r () in
        let iterating = fresh_r () in
        let assign_rv_empty = Basic (Assignment (mk_assign rv (Expression (Literal Empty)))) in
        let label1 = fresh_r () in
        let r3_stmts, r3 = f e1 in
        let r1_stmts, r1 = translate_exp ctx e2 in
        let r2_stmts, r2 = translate_gamma r1 ctx in
          [
            assign_rv_empty; 
            Basic (Assignment (mk_assign iterating (Expression (Literal (Bool true)))));
            Label label1;
            Sugar (If (equal_bool_expr iterating true, 
                r3_stmts @ 
                [ 
                  Sugar (If (equal_empty_expr r3, 
                    [], 
                    [Basic (Assignment (mk_assign rv (Expression (Var r3))))]));
                ] @
                r1_stmts @ 
                r2_stmts @ 
                [     
                  Sugar (If (is_false_expr r2,
                    [Basic (Assignment (mk_assign iterating (Expression (Literal (Bool false)))))],
                    []));
                  Goto label1
                ], 
                
                []))
          ], rv

        
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
        let exit_label = fresh_r () in
        let throw_var = fresh_r () in
        let new_ctx = {ctx with label_throw = catch_label; label_return = return_finally_label; throw_var = throw_var} in
        let r1_stmts, r1 = translate_stmt new_ctx e1 in
        let rv = fresh_r () in
        
        let catch_id = "catch" ^ fresh_r () in
        let catch_scope = catch_id ^ "_scope" in
        
        let catch_ctx = {ctx with 
          env_vars = (make_ctx_vars catch_id [id]) :: ctx.env_vars;
          label_throw = throw_finally_label;
          label_return = return_finally_label;
        } in
        let r2_stmts, r2 = translate_stmt catch_ctx e2 in
        let r3_stmts, r3 = f e3 in
            
        r1_stmts @
        [
          Basic (Assignment (mk_assign rv (Expression (Var r1))));
          Goto finally_label;
          Label catch_label;
          Basic (Assignment (mk_assign catch_scope Obj));
          add_proto_null catch_scope;
          Basic (Mutation (mk_mutation (Var catch_scope) (Literal (String id)) (Var throw_var)))
        ] @
        r2_stmts @
        [
          Basic (Assignment (mk_assign rv (Expression (Var r2))));
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
          Goto ctx.label_throw;
          Label exit_label
        ], rv
        
      | Parser_syntax.Try (e1, None, Some e3) ->
        let return_finally_label = "finally." ^ fresh_r () in
        let throw_finally_label = "finally." ^ fresh_r () in
        let exit_label = fresh_r () in
        let new_ctx = {ctx with label_throw = throw_finally_label; label_return = return_finally_label} in
        let r1_stmts, r1 = translate_stmt new_ctx e1 in
        let r3_stmts, r3 = f e3 in
            
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
        [
          Goto ctx.label_throw;
          Label exit_label
        ], r1
        
      | Parser_syntax.Try (e1, Some (id, e2), None) ->
        let catch_label = "catch." ^ fresh_r () in
        let exit_label = fresh_r () in
        let throw_var = fresh_r () in
        let new_ctx = {ctx with label_throw = catch_label; throw_var = throw_var} in
        let r1_stmts, r1 = translate_stmt new_ctx e1 in
        let rv = fresh_r () in
        
        let catch_id = "catch" ^ fresh_r () in
        let catch_scope = catch_id ^ "_scope" in
        
        let catch_ctx = {ctx with 
          env_vars = (make_ctx_vars catch_id [id]) :: ctx.env_vars;
        } in
        let r2_stmts, r2 = translate_stmt catch_ctx e2 in
            
        r1_stmts @
        [
          Basic (Assignment (mk_assign rv (Expression (Var r1))));
          Goto exit_label;
          Label catch_label;
          Basic (Assignment (mk_assign catch_scope Obj));
          add_proto_null catch_scope;
          Basic (Mutation (mk_mutation (Var catch_scope) (Literal (String id)) (Var throw_var)))
        ] @
        r2_stmts @
        [
          Basic (Assignment (mk_assign rv (Expression (Var r2))));
          Goto exit_label;
          Label exit_label;
        ], rv  
        
      | Parser_syntax.Try _ -> raise (PulpInvalid "Try _ None None")
        
      | Parser_syntax.Throw e ->
        let r1_stmts, r1 = translate_exp ctx e in
        let r2_stmts, r2 = translate_gamma r1 ctx in 
        
        r1_stmts @ 
        r2_stmts @
        [ Basic (Assignment (mk_assign ctx.throw_var (Expression (Var r2))));
          Goto ctx.label_throw], r2

      (* Next TODO *) 
      | Parser_syntax.Continue _ -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:12.7 The continue Statement.")))  
      | Parser_syntax.Break _ -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:12.8 The break Statement.")))
      | Parser_syntax.Label _ -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:12.12 Labelled Statement.")))
        
      | Parser_syntax.For _ -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:12.6.3 The for Statement.")))
      | Parser_syntax.Switch _ -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:12.11 Switch Statement.")))

      (* I am not considering those *)  
      
      | Parser_syntax.ForIn _ -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:12.6.4 The for-in Statement.")))
      | Parser_syntax.With _ -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:12.10 With Statemenet.")))
      | Parser_syntax.Debugger -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:12.15 The debugger Statement.")))

      

let exp_to_elem ctx exp : statement list * variable = 
    let r = fresh_r() in
    match exp.Parser_syntax.exp_stx with
      | Parser_syntax.NamedFun (s, name, args, body) -> [Basic (Assignment (mk_assign r (Expression (Literal Empty))))], r (* Things done already *)
      | _ ->  translate_stmt ctx exp

let rec exp_to_fb ctx exp : statement list * variable =
  match exp.Parser_syntax.exp_stx with
    | Parser_syntax.Script (_, es) 
    | Parser_syntax.Block (es) -> translate_block es (exp_to_elem ctx)
    | _ -> exp_to_elem ctx exp
        
let translate_function fb fid main args env named =
  let ctx = create_ctx env in
  
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
      | Parser_syntax.NamedFun (_, name, _, body) -> 
        let stmts, lvar = translate_function_expression f ctx None in
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
      [Basic (Assignment (mk_assign ctx.return_var (Expression (Var lvar))))]
    else
      [Basic (Assignment (mk_assign ctx.return_var (Expression (Literal Empty))))] in
    
  let pulpe = 
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
  
  make_function_block fid pulpe (rthis :: (rscope :: args)) ctx

let translate_function_syntax level id e named env main =
  let pulpe = 
    match e.Parser_syntax.exp_stx with
      | Parser_syntax.AnnonymousFun (_, args, fb) -> translate_function fb id main args env None
      | Parser_syntax.NamedFun (_, name, args, fb) -> translate_function fb id main args env named
      | Parser_syntax.Script (_, es) -> translate_function e main main [] env None
      | _ -> raise (Invalid_argument "Should be a function definition here") in
  match level with
    | IVL_buitin_functions -> raise (Utils.InvalidArgument ("pulp_Translate", "builtin_functions level not implemented yet"))
    | IVL_conditionals -> pulpe
    | IVL_goto -> {pulpe with func_body = to_ivl_goto pulpe.func_body}

let exp_to_pulp level e main =
  let context = AllFunctions.empty in
  let e = add_codenames main e in
  let all_functions = get_all_functions_with_env_in_fb [] e main in
    
  let context = List.fold_left (fun c (fexpr, fnamed, fenv) -> 
    let fid = get_codename fexpr in
    let fb = translate_function_syntax level fid fexpr fnamed fenv main in
    AllFunctions.add fid fb c
   ) context all_functions in
  context
