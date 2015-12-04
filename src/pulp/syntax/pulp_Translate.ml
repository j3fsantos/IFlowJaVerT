open Batteries
open Pulp_Syntax
open Pulp_Syntax_Utils
open Pulp_Syntax_Print
open Pulp_Procedure
open Pulp_Translate_Aux

exception PulpNotImplemented of string
exception PulpInvalid of string

type translation_level =
  | IVL_buitin_functions
  | IVL_conditionals
  | IVL_goto_unfold_functions
  | IVL_goto
  | IVL_goto_with_get_value

type switch_record = { (* Special constants for throws and returns *)
    a_cases : (Parser_syntax.exp * Parser_syntax.exp) list; 
		b_cases : (Parser_syntax.exp * Parser_syntax.exp) list; 
		default : Parser_syntax.exp option
}	

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
         
let translate_to_number_bin_op f op e1 e2 ctx =
  let r1_stmts, r1 = f e1 in
  let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
  let r3_stmts, r3 = f e2 in
  let r4_stmts, r4 = spec_func_call (GetValue (Var r3)) ctx in
  let r5_stmts, r5 = spec_func_call (ToNumber (Var r2)) ctx in
  let r6_stmts, r6 = spec_func_call (ToNumber (Var r4)) ctx in 
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
  let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
  let r3_stmts, r3 = f e2 in
  let r4_stmts, r4 = spec_func_call (GetValue (Var r3)) ctx in
  let r2_to_number, r2_number = spec_func_call (ToNumber (Var r2)) ctx in
  let r4_to_number, r4_number = spec_func_call (ToNumber (Var r4)) ctx in
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
  let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
  let r3_stmts, r3 = f e2 in
  let r4_stmts, r4 = spec_func_call (GetValue (Var r3)) ctx in
  let r2_to_number, r2_number = spec_func_call (ToNumber (Var r2)) ctx in
  let r4_to_number, r4_number = spec_func_call (ToNumber (Var r4)) ctx in
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
  let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
  let r3_stmts, r3 = f e2 in
  let r4_stmts, r4 = spec_func_call (GetValue (Var r3)) ctx in
  let rv = fresh_r () in
  let assign_rv rvar e = Basic (Assignment (mk_assign rvar (Expression e))) in 
  let exit_label = fresh_r () in
  let types_equal_stmts_1, rv1 = spec_func_call (StrictEqualitySameType (Var r2, Var r4)) ctx in
  let y1_to_prim = fresh_r () in
  let to_primitive_y1, y1_prim = spec_func_call (ToPrimitive (Var r4, None)) ctx in
  let x1_to_prim = fresh_r () in
  let to_primitive_x1, x1_prim = spec_func_call (ToPrimitive (Var r2, None)) ctx in
  let x2_to_number = fresh_r () in
  let to_number_x2, x2_number = spec_func_call (ToNumberPrim (Var x1_to_prim)) ctx in
  let y2_to_number = fresh_r () in
  let to_number_y2, y2_number = spec_func_call (ToNumberPrim (Var y1_to_prim)) ctx in
  let y3 = fresh_r () in
  let to_number_y3, y3_number = spec_func_call (ToNumberPrim (Var y2_to_number)) ctx in
  let x3 = fresh_r () in
  let to_number_x3, x3_number = spec_func_call (ToNumberPrim (Var x2_to_number)) ctx in
  let types_equal_stmts_2, rv2 = spec_func_call (StrictEqualitySameType (Var x3, Var y3)) ctx in
    r1_stmts @ 
    r2_stmts @ 
    r3_stmts @  
    r4_stmts @  
    [ 
      Sugar (If (equal_exprs (TypeOf (Var r2)) (TypeOf (Var r4)),
        types_equal_stmts_1 @ [assign_rv rv (Var rv1); Goto exit_label],
		    [ 
		      Sugar (If (type_of_exp (Var r4) (ObjectType None),
		        to_primitive_y1 @ [assign_rv y1_to_prim (Var y1_prim)],
		        [assign_rv y1_to_prim (Var r4)]));
		      Sugar (If (type_of_exp (Var r2) (ObjectType None),
		          to_primitive_x1 @ [assign_rv x1_to_prim (Var x1_prim)],
		          [assign_rv x1_to_prim (Var r2)]));
		      Sugar (If (type_of_exp (Var x1_to_prim) BooleanType,
		        to_number_x2 @ [assign_rv x2_to_number (Var x2_number)],
            [ assign_rv x2_to_number (Var x1_to_prim)]));
		      Sugar (If (type_of_exp (Var y1_to_prim) BooleanType,
		          to_number_y2 @ [assign_rv y2_to_number (Var y2_number)],
              [ assign_rv y2_to_number (Var y1_to_prim)]));
          Sugar (If (or_expr 
                    (and_expr (equal_null_expr (Var x2_to_number)) (equal_undef_expr (Var y2_to_number))) 
                    (and_expr (equal_undef_expr (Var x2_to_number)) (equal_null_expr (Var y2_to_number))),
            [assign_rv rv (Literal (Bool true))] @ [Goto exit_label],
            []));
          Sugar (If (and_expr (type_of_exp (Var x2_to_number) NumberType) (type_of_exp (Var y2_to_number) StringType),
              to_number_y3 @ [assign_rv y3 (Var y3_number)],
              [ assign_rv y3 (Var y2_to_number)]));
          Sugar (If (and_expr (type_of_exp (Var x2_to_number) StringType) (type_of_exp (Var y2_to_number) NumberType),
              to_number_x3 @ [assign_rv x3 (Var x3_number)],
             [ assign_rv x3 (Var x2_to_number)]));
          Sugar (If (equal_exprs (TypeOf (Var x3)) (TypeOf (Var y3)),
            types_equal_stmts_2 @ [assign_rv rv (Var rv2); Goto exit_label],
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
  let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
  let r3_stmts, r3 = f e2 in
  let r4_stmts, r4 = spec_func_call (GetValue (Var r3)) ctx in
  let r5_stmts, lprim = spec_func_call (ToPrimitive (Var r2, None)) ctx in
  let r6_stmts, rprim = spec_func_call (ToPrimitive (Var r4, None)) ctx in
  let r7_stmt, lstring = spec_func_call (ToStringPrim (Var lprim)) ctx in
  let r8_stmt, rstring = spec_func_call (ToStringPrim (Var rprim)) ctx in  
  let r9_stmt, lnum = spec_func_call (ToNumberPrim (Var lprim)) ctx in
  let r10_stmt, rnum = spec_func_call (ToNumberPrim (Var rprim)) ctx in
  let rv = fresh_r () in
  let assign_rv_expr e = Basic (Assignment (mk_assign rv (Expression e))) in
    r1_stmts @ 
    r2_stmts @ 
    r3_stmts @ 
    r4_stmts @
    r5_stmts @
    r6_stmts @
    [ Sugar (If (or_expr 
                  (type_of_exp (Var lprim) StringType)
                  (type_of_exp (Var rprim) StringType),
      r7_stmt @ r8_stmt @ [assign_rv_expr (BinOp (Var lstring, Concat, Var rstring))],
      r9_stmt @ r10_stmt @ [assign_rv_expr (BinOp (Var lnum, Arith Plus, Var rnum))]))
    ], rv
  
   
let translate_bin_op_logical f e1 e2 bop ctx =
  let op = tr_boolean_op bop in
  let r1_stmts, r1 = f e1 in
  let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
  let rv = fresh_r () in
  let r3_stmts, r3 = f e2 in
  let r4_stmts, r4 = spec_func_call (GetValue (Var r3)) ctx in
  let to_boolean, r5 = spec_func_call (ToBoolean (Var r2)) ctx in
    r1_stmts @  
    r2_stmts @  
    to_boolean @
    [
      Sugar (If ((if (op = And) then (equal_bool_expr (Var r5) false) else (equal_bool_expr (Var r5) true)), 
        [Basic (Assignment (mk_assign rv (Expression (Var r2))))], 
	      r3_stmts @  
        r4_stmts @  
	      [ Basic (Assignment (mk_assign rv (Expression (Var r4))))]))
    ], rv
  
let find_var_scope var env =
  try 
  let scope = List.find (fun scope ->
    List.exists (fun v -> v = var) scope.fun_bindings
    ) env in
  Some (Var (function_scope_name (scope.func_id)))
  with
    | Not_found -> None


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
  let o = fresh_r () in
  let get_stmts = translate_get f (literal_builtin_field FPrototype) o in
  let proto = mk_assign_fresh (Lookup (v, literal_builtin_field FProto)) in
  let proto_o = mk_assign_fresh (ProtoO (Var proto.assign_left, Var o)) in
  [ Sugar (If (type_of_exp v (ObjectType None), 
    get_stmts @
    [ Sugar (If (type_of_exp (Var o) (ObjectType None),
      [ Basic (Assignment proto);
        Basic (Assignment proto_o);
        Basic (Assignment (mk_assign rv (Expression (Var proto_o.assign_left))))
      ],
      translate_error_throw Ltep ctx.throw_var ctx.label_throw))
    ],
    [Basic (Assignment (mk_assign rv (Expression (Literal (Bool false)))))]))
  ], rv
  
let translate_inc_dec f e op ctx =
  let r1_stmts, r1 = f e in
  let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
  let to_number_stmts, oldvalue = spec_func_call (ToNumber (Var r2)) ctx in
  let newvalue = mk_assign_fresh_e (BinOp (Var oldvalue, Arith op, (Literal (Num 1.0)))) in     
  let putvalue_stmts, _ = spec_func_call (PutValue (Var r1 , Var newvalue.assign_left)) ctx in  
    r1_stmts @  
    [Sugar (If (and_expr (type_of_vref (Var r1))
                  (or_expr 
                  (equal_string_exprs (Field (Var r1)) "arguments") 
                  (equal_string_exprs (Field (Var r1)) "eval")), 
      translate_error_throw LSError ctx.throw_var ctx.label_throw, 
      r2_stmts @  
      to_number_stmts @
      [Basic (Assignment newvalue)] @ 
      putvalue_stmts))
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
          let rv = fresh_r () in
          match scope with
            | Some scope -> 
              [assign_expr rv (Ref (scope, Literal (String v) , VariableReference))], rv    
            | None -> 
              let r1 = mk_assign_fresh (ProtoF (Literal (LLoc Lg), Literal (String v))) in
              [ Basic (Assignment r1);
                Sugar (If (equal_empty_expr (Var r1.assign_left), 
                  [ assign_expr rv (Ref (Literal Undefined, Literal (String v) , VariableReference)) ], 
                  [ assign_expr rv (Ref (Literal (LLoc Lg), Literal (String v) , VariableReference)) ]));
              ], rv     
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
                  let r3_stmts, r3 = spec_func_call (GetValue (Var r2)) ctx in 
                  let propname_stmts, propname_expr = 
                    match prop_name with
                      | Parser_syntax.PropnameId s
                      | Parser_syntax.PropnameString s -> [],  Literal (String s)
                      | Parser_syntax.PropnameNum f -> 
                        begin
                          let f_var = mk_assign_fresh_e (Literal (Num f)) in
                          let propname_to_string, lvar = spec_func_call (ToStringPrim (Var f_var.assign_left)) ctx in 
                          [ Basic (Assignment f_var) ]
                          @  propname_to_string, Var lvar
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
          let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
          let r4_stmts, _ = spec_func_call (CheckObjectCoercible (Var r2)) ctx in
          let r5 = mk_assign_fresh_e (Ref (Var r2, Literal (String v), MemberReference)) in
            r1_stmts @ 
            r2_stmts @ 
            r4_stmts @
            [Basic (Assignment r5)], r5.assign_left
        
      | Parser_syntax.CAccess (e1, e2) ->
          let r1_stmts, r1 = f e1 in
          let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
          let r3_stmts, r3 = f e2 in
          let r4_stmts, r4 = spec_func_call (GetValue (Var r3)) ctx in
          let r5_stmts, _ = spec_func_call (CheckObjectCoercible (Var r2)) ctx in
          let r4_to_string, r4_string = spec_func_call (ToString (Var r4)) ctx in
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
        let if3, call_lvar = translate_inner_call (Var r2) (Var vthis.assign_left) arg_values ctx.throw_var ctx.label_throw [] (* Cannot be new eval *) in (* TODO Construct vs. Call *)    
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
          [ Sugar (If (type_of_exp (Var r2) (ObjectType (Some Builtin)),
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
	            Sugar (If (type_of_obj (Var prototype.assign_left), 
	                [Basic (Assignment (mk_assign vthisproto (Expression (Var prototype.assign_left))))], 
	                [Basic (Assignment (mk_assign vthisproto (Expression (Literal (LLoc Lop)))))])); 
	            Basic (Assignment vthis);
	            add_proto_var vthis.assign_left vthisproto 
	          ] @
	          if3 @ 
	          [  Sugar (If (type_of_obj (Var call_lvar), 
	                [Basic (Assignment (mk_assign rv (Expression (Var call_lvar))))], 
	                [Basic (Assignment (mk_assign rv (Expression (Var vthis.assign_left))))]))
	          ]))
          ], rv
        
      | Parser_syntax.Call (e1, e2s) ->
        let stmts, r1, r2, arg_values = translate_call_construct_start f e1 e2s ctx false in
              let vthis = fresh_r () in
              let assign_vthis_und = Basic (Assignment (mk_assign vthis (Expression (Literal Undefined)))) in
              let if5, call = translate_inner_call (Var r2) (Var vthis) arg_values ctx.throw_var ctx.label_throw ctx.env_vars in
          stmts @ 
          [
            Sugar (If (type_of_ref (Var r1), 
                [
                  Sugar (If (type_of_vref (Var r1), 
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
            let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
            let rv = fresh_r () in 
            let to_boolean, r3 = spec_func_call (ToBoolean (Var r2)) ctx in
            let if1 = 
              Sugar (If (equal_bool_expr (Var r3) false, 
                [
                  Basic (Assignment (mk_assign rv (Expression (Literal (Bool true)))))
                ], 
                [
                  Basic (Assignment (mk_assign rv (Expression (Literal (Bool false)))))
                ])) in
                r1_stmts @
                r2_stmts @
                to_boolean @
                [if1], rv
          | Parser_syntax.TypeOf -> 
            begin
              let rv = fresh_r () in
              let r1_stmts, r1 = f e in
              let base = mk_assign_fresh (Expression (Base (Var r1))) in
              let value = fresh_r () in
              let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
              let hasfield = mk_assign_fresh (HasField (Var value, literal_builtin_field FId)) in
              let exit_label = fresh_r () in
              let assign_rv v = 
                [Basic (Assignment (mk_assign rv (Expression (Literal (String v)))));
                 Goto exit_label] in
              r1_stmts @
              [
                Sugar (If (type_of_ref (Var r1),
                [
                  Basic (Assignment base);
                  Sugar (If (equal_undef_expr (Var base.assign_left),
                   assign_rv "undefined",
                   r2_stmts @
                   [ Basic (Assignment (mk_assign value (Expression (Var r2)))) ]))
                ],
                [Basic (Assignment (mk_assign value (Expression (Var r1))))]));
                Sugar (If (type_of_exp (Var value) UndefinedType,
                  assign_rv "undefined",
                  [Sugar (If (type_of_exp (Var value) NullType,
                    assign_rv "object",
                    [Sugar (If (type_of_exp (Var value) BooleanType,
                      assign_rv "boolean",
                      [Sugar (If (type_of_exp (Var value) NumberType,
                        assign_rv "number",
                        [Sugar (If (type_of_exp (Var value) StringType,
                          assign_rv "string",
                          (* Must be an object *)
                          [ Basic (Assignment hasfield);
                            Sugar (If (equal_bool_expr (Var hasfield.assign_left) true,
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
            let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
            let r3_stmts, r3 = spec_func_call (ToNumber (Var r2)) ctx in
            r1_stmts @
            r2_stmts @
            r3_stmts, r3
					| Parser_syntax.Negative -> 
            let r1_stmts, r1 = f e in
            let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
            let r3_stmts, r3 = spec_func_call (ToNumber (Var r2)) ctx in
            let rv = fresh_r () in
            let assign_rv n = [Basic (Assignment (mk_assign rv (Expression n)))] in
            let negative = mk_assign_fresh_e (UnaryOp (Negative, (Var r3))) in
            r1_stmts @
            r2_stmts @
            r3_stmts @
            [ Sugar (If (equal_num_expr (Var r3) nan,
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
            let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
            let r2_to_number, r2_number = spec_func_call (ToNumber (Var r2)) ctx in
            let r3 = mk_assign_fresh_e (UnaryOp (ToInt32Op, Var r2_number)) in
            let r4 = mk_assign_fresh_e (UnaryOp (BitwiseNot, Var r3.assign_left)) in
            r1_stmts @
            r2_stmts @
            r2_to_number @
            [Basic (Assignment r3);
             Basic (Assignment r4)], r4.assign_left
		      | Parser_syntax.Void -> 
            let r1_stmts, r1 = f e in
            let r2_stmts, _ = spec_func_call (GetValue (Var r1)) ctx in
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
            Sugar (If (type_of_ref (Var r1), 
                [ Basic (Assignment r4);
                  Sugar (If (equal_undef_expr (Var r4.assign_left), 
                    gotothrow, 
                    [])); 
                  Sugar (If (type_of_vref (Var r1), 
                    gotothrow, 
                    [])); 
                  Basic (Assignment r3);  
                  Basic (Assignment r2); 
                  Sugar (If (equal_bool_expr (Var r2.assign_left) false, 
                    [Basic (Assignment assign_rv_true)], 
                    [
                      Basic (Assignment r5); 
                      Sugar (If (and_expr 
                                (equal_exprs (Var r3.assign_left) (literal_builtin_field FPrototype)) 
                                (equal_bool_expr (Var r5.assign_left) true), 
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
								  let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
								  let r3_stmts, r3 = f e2 in
								  let r4_stmts, r4 = spec_func_call (GetValue (Var r3)) ctx in
								  let r5, rv = spec_func_call (StrictEquality (Var r2, Var r4)) ctx in
								    r1_stmts @ 
								    r2_stmts @ 
								    r3_stmts @ 
								    r4_stmts @ 
								    r5, rv
						  | Parser_syntax.NotTripleEqual ->
                  let r1_stmts, r1 = f e1 in
                  let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
                  let r3_stmts, r3 = f e2 in
                  let r4_stmts, r4 = spec_func_call (GetValue (Var r3)) ctx in
                  let r5, rv = spec_func_call (StrictEquality (Var r2, Var r4)) ctx in
                  let r6 = mk_assign_fresh (Expression (UnaryOp (Not, (Var rv)))) in
                    r1_stmts @ 
                    r2_stmts @ 
                    r3_stmts @ 
                    r4_stmts @ 
                    r5 @
                    [ Basic (Assignment r6)], r6.assign_left
						  | Parser_syntax.Lt -> 
                  let r1_stmts, r1 = f e1 in
								  let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
								  let r3_stmts, r3 = f e2 in
								  let r4_stmts, r4 = spec_func_call (GetValue (Var r3)) ctx in
                  let r5_stmts, r5 = spec_func_call (AbstractEquality (Var r2, Var r4, true)) ctx in
                  let rv = fresh_r() in
                  let assign_rv v = Basic (Assignment (mk_assign rv (Expression v))) in                  
								    r1_stmts @ 
								    r2_stmts @ 
								    r3_stmts @ 
								    r4_stmts @
                    r5_stmts @ 
								    [Sugar (If (equal_undef_expr (Var r5), 
                      [assign_rv (Literal (Bool false))], 
                      [assign_rv (Var r5)]))
                    ], rv
						  | Parser_syntax.Le -> 
                  let r1_stmts, r1 = f e1 in
                  let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
                  let r3_stmts, r3 = f e2 in
                  let r4_stmts, r4 = spec_func_call (GetValue (Var r3)) ctx in
                  let r5_stmts, r5 = spec_func_call (AbstractEquality (Var r4, Var r2, false)) ctx in
                  let rv = fresh_r() in
                  let assign_rv v = Basic (Assignment (mk_assign rv (Expression v))) in                  
                    r1_stmts @ 
                    r2_stmts @ 
                    r3_stmts @ 
                    r4_stmts @
                    r5_stmts @ 
                    [Sugar (If (or_expr (equal_bool_expr (Var r5) true) (equal_undef_expr (Var r5)), 
                      [assign_rv (Literal (Bool false))], 
                      [assign_rv (Literal (Bool true))]))
                    ], rv
						  | Parser_syntax.Gt -> 
                  let r1_stmts, r1 = f e1 in
                  let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
                  let r3_stmts, r3 = f e2 in
                  let r4_stmts, r4 = spec_func_call (GetValue (Var r3)) ctx in
                  let r5_stmts, r5 = spec_func_call (AbstractEquality (Var r4, Var r2, false)) ctx in
                  let rv = fresh_r() in
                  let assign_rv v = Basic (Assignment (mk_assign rv (Expression v))) in                  
                    r1_stmts @ 
                    r2_stmts @ 
                    r3_stmts @ 
                    r4_stmts @
                    r5_stmts @ 
                    [Sugar (If (equal_undef_expr (Var r5), 
                      [assign_rv (Literal (Bool false))], 
                      [assign_rv (Var r5)]))
                    ], rv
						  | Parser_syntax.Ge -> 
                  let r1_stmts, r1 = f e1 in
                  let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
                  let r3_stmts, r3 = f e2 in
                  let r4_stmts, r4 = spec_func_call (GetValue (Var r3)) ctx in
                  let r5_stmts, r5 = spec_func_call (AbstractEquality (Var r2, Var r4, true)) ctx in
                  let rv = fresh_r() in
                  let assign_rv v = Basic (Assignment (mk_assign rv (Expression v))) in                  
                    r1_stmts @ 
                    r2_stmts @ 
                    r3_stmts @ 
                    r4_stmts @
                    r5_stmts @ 
                    [Sugar (If (or_expr (equal_bool_expr (Var r5) true) (equal_undef_expr (Var r5)), 
                      [assign_rv (Literal (Bool false))], 
                      [assign_rv (Literal (Bool true))]))
                    ], rv
			 | Parser_syntax.In -> 
                let r1_stmts, r1 = f e1 in
                let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
                let r3_stmts, r3 = f e2 in
                let r4_stmts, r4 = spec_func_call (GetValue (Var r3)) ctx in
                let r5_stmts, r5 = spec_func_call (ToString (Var r2)) ctx in
                let r6_stmts, r6 = spec_func_call (HasProperty (Var r4, Var r5)) ctx in
                r1_stmts @ 
                r2_stmts @ 
                r3_stmts @ 
                r4_stmts @
                [ Sugar (If (type_of_exp (Var r4) (ObjectType None), 
                    r5_stmts @ r6_stmts,
                    translate_error_throw Ltep ctx.throw_var ctx.label_throw))
                ], r6
			| Parser_syntax.InstanceOf -> 
                let r1_stmts, r1 = f e1 in
                let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
                let r3_stmts, r3 = f e2 in
                let r4_stmts, r4 = spec_func_call (GetValue (Var r3)) ctx in
                let hasfield = mk_assign_fresh (HasField (Var r4, literal_builtin_field FId)) in
                let gotothrow = translate_error_throw Ltep ctx.throw_var ctx.label_throw in
                let r5_stmts, r5 = translate_has_instance (Var r4) (Var r2) ctx in
                r1_stmts @ 
                r2_stmts @ 
                r3_stmts @ 
                r4_stmts @
                [ Sugar (If (type_of_exp (Var r4) (ObjectType None), 
                    [ Basic (Assignment hasfield);
                      Sugar (If (equal_bool_expr (Var hasfield.assign_left) false, (* [[HasInstance]] *)
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
          let r3_stmts, r3 = spec_func_call (GetValue (Var r2)) ctx in
          let r4 = mk_assign_fresh_e (Field (Var r1)) in
          let gotothrow = translate_error_throw Lrep ctx.throw_var ctx.label_throw in
          let putvalue_stmts, _ = spec_func_call (PutValue (Var r1 , Var r3)) ctx in
            r1_stmts @
            r2_stmts @
            r3_stmts @
            [
              Sugar (If (type_of_vref (Var r1), 
                    [
                      Basic (Assignment r4);
                      Sugar (If (or_expr 
                             (equal_string_expr (Var r4.assign_left) "arguments") 
                             (equal_string_expr (Var r4.assign_left) "eval"), gotothrow, []));
                    ], 
                    []))
            ] @
            putvalue_stmts, r3
        end
      
      | Parser_syntax.Array _ -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:11.1.4 Array Initialiser.")))
      | Parser_syntax.ConditionalOp (e1, e2, e3) ->
        let r1_stmts, r1 = f e1 in
        let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
        let r3_stmts, r3 = f e2 in
        let r4_stmts, r4 = spec_func_call (GetValue (Var r3)) ctx in
        let r5_stmts, r5 = f e3 in
        let r6_stmts, r6 = spec_func_call (GetValue (Var r5)) ctx in
        let to_boolean, r7 = spec_func_call (ToBoolean (Var r2)) ctx in
        let rv = fresh_r () in     
          r1_stmts @
          r2_stmts @ 
          to_boolean @
          [ Sugar (If (equal_bool_expr (Var r7) true, 
            r3_stmts @ 
            r4_stmts @ 
            [Basic (Assignment (mk_assign rv (Expression (Var r4))))], 
            r5_stmts @
            r6_stmts @ 
            [Basic (Assignment (mk_assign rv (Expression (Var r6))))]))
          ], rv
      | Parser_syntax.AssignOp (e1, aop, e2) -> 
          let r1_stmts, r1 = f e1 in
				  let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
				  let r3_stmts, r3 = f e2 in
				  let r4_stmts, r4 = spec_func_call (GetValue (Var r3)) ctx in
				  let r5 = mk_assign_fresh_e (BinOp (Var r2, tr_bin_op (Parser_syntax.Arith aop), Var r4)) in
          let field = mk_assign_fresh_e (Field (Var r1)) in
          let putvalue_stmts, _ = spec_func_call (PutValue (Var r1 , Var r5.assign_left)) ctx in
				    r1_stmts @ 
				    r2_stmts @ 
				    r3_stmts @
            r4_stmts @ 
				    [
             Basic (Assignment r5);
             Sugar (If (type_of_vref (Var r1),
		          [Basic (Assignment field);
               Sugar (If (or_expr 
                             (equal_string_expr (Var field.assign_left) "arguments") 
                             (equal_string_expr (Var field.assign_left) "eval"), 
                 translate_error_throw LSError ctx.throw_var ctx.label_throw, 
                 []))
              ],
		          []));] @
            putvalue_stmts,
				    r5.assign_left

      | Parser_syntax.Comma (e1, e2) -> 
        let r1_stmts, r1 = f e1 in
        let r2_stmts, _ = spec_func_call (GetValue (Var r1)) ctx in
        let r3_stmts, r3 = f e2 in
        let r4_stmts, r4 = spec_func_call (GetValue (Var r3)) ctx in
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
        let gamma_stmts, r2  = spec_func_call (GetValue (Var r1)) ctx in
				let ret_val_stmts = [ 
          Sugar (If (equal_empty_expr (Var r2), 
            [ ], 
            [
              Basic (Assignment (mk_assign ret_def (Expression (Var r2))))
            ]))] in 
        stmts @ gamma_stmts @ ret_val_stmts, ret_def

      | Parser_syntax.AnnonymousFun _
      | Parser_syntax.NamedFun _ -> raise (PulpInvalid ("Expected statement not Function Declaration. Actual " ^ (Pretty_print.string_of_exp true exp)))
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
        let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
        let r3_stmts, r3 = f e2 in
        let to_boolean, r5 = spec_func_call (ToBoolean  (Var r2)) ctx in
        let elsebranch = match e3 with
          | Some e3 -> 
            let r4_stmts, r4 = f e3 in
            r4_stmts
          | None -> [] in      
          r1_stmts @ 
          r2_stmts @ 
          to_boolean @
          [ Sugar (If (equal_bool_expr (Var r5) true, 
              r3_stmts, 
              elsebranch))
          ], ret_def
           
      | Parser_syntax.While (e1, e2) ->
        let r1_stmts, r1 = translate_exp ctx e1 in
        let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
        let continue = "continue" ^ (fresh_r ()) in
        let break = "break" ^ (fresh_r ()) in
        let new_ctx = {ctx with
          label_continue = (("", continue) :: (List.map (fun l -> (l, continue)) labelset)) @ ctx.label_continue;
          label_break = (("", break) :: (List.map (fun l -> (l, break)) labelset)) @ ctx.label_break
        } in
        let r3_stmts, r3 = translate_stmt new_ctx [] e2 in
        let to_boolean, r4 = spec_func_call (ToBoolean (Var r2)) ctx in
          [
            Label continue
          ] @ 
          r1_stmts @ 
          r2_stmts @ 
          to_boolean @
          [ Sugar (If (equal_bool_expr (Var r4) true, 
              r3_stmts @ 
              [ Goto continue ],                 
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
        let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
        let to_boolean, r4 = spec_func_call (ToBoolean (Var r2)) ctx in
          [
            Basic (Assignment (mk_assign iterating (Expression (Literal (Bool true)))));
            Label label1;
            Sugar (If (equal_bool_expr (Var iterating) true, 
                r3_stmts @ 
                [ Label continue ] @
                r1_stmts @ 
                r2_stmts @ 
                to_boolean @
                [ Sugar (If (equal_bool_expr (Var r4) false,
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
            let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in
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
        
        let translate_finally_body () = 
          let r3_stmts, _ = f e3 in
          r3_stmts in
        
        let continue_finally_stmts = List.map (fun ((_, c1), (_, c2)) ->
          [Label c1] @
          (translate_finally_body ()) @
          [Goto c2]
        ) (List.combine continue_finally_label ctx.label_continue) in
        
        let break_finally_stmts = List.map (fun ((_, b1), (_, b2)) ->
          [Label b1] @
          (translate_finally_body ()) @
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
        (translate_finally_body ()) @
        [
          Goto exit_label;
          Label return_finally_label      
        ] @
        (translate_finally_body ()) @
        [
          Goto ctx.label_return;
          Label throw_finally_label      
        ] @
        (translate_finally_body ()) @
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
        let exit_label = "exit." ^ (fresh_r ()) in
        let new_ctx = {ctx with 
          label_throw = throw_finally_label; 
          label_return = return_finally_label;
          label_continue = continue_finally_label;
          label_break = break_finally_label;
        } in
        
        let translate_finally_body () = 
          let r3_stmts, _ = f e3 in
          r3_stmts in
        
        let r1_stmts, r1 = translate_stmt new_ctx [] e1 in
        
        let continue_finally_stmts = List.map (fun ((_, c1), (_, c2)) ->
          [Label c1] @
          (translate_finally_body ()) @
          [Goto c2]
        ) (List.combine continue_finally_label ctx.label_continue) in
        
        let break_finally_stmts = List.map (fun ((_, b1), (_, b2)) ->
          [Label b1] @
          (translate_finally_body ()) @
          [Goto b2]
        ) (List.combine break_finally_label ctx.label_break) in
            
        r1_stmts @
        (translate_finally_body ()) @
        [
          Goto exit_label;
          Label return_finally_label      
        ] @
        (translate_finally_body ()) @
        [
          Goto ctx.label_return;
          Label throw_finally_label      
        ] @
        (translate_finally_body ()) @
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
        let r2_stmts, r2 = spec_func_call (GetValue (Var r1)) ctx in 
        
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
					 | Some e -> spec_func_call (GetValue (Var r21)) ctx in
		    
				let r23_stmts, r23 = match e2 with
				   | None -> [ ], r_test_none
					 | Some e -> spec_func_call (ToBoolean (Var r22)) ctx in
					
				let r3_stmts, _ = match e3 with 
				   | None -> [ ], r_incr_none (* Basic (Assignment (mk_assign r_incr_none (Expression (Literal (Empty))))) *)
					 | Some e -> translate_exp ctx e in
							
				let r4_stmts, r4 = translate_stmt new_ctx [] e4 in
				
				(* let r1 = mk_assign_fresh_lit (String "banana") in *)
          r1_stmts @  
					[ Label label1 ] @ 
					r21_stmts @ r22_stmts @ r23_stmts @
					[ Sugar (If (equal_bool_expr (Var r23) true,
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
				let r_test_stmts2, r_test2 = spec_func_call (GetValue (Var r_test1)) ctx in
				let break = fresh_r () in
				let r_found_a = fresh_r () in
				let r_found_b = fresh_r () in
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
					let r_case_stmts2, r_case2 = spec_func_call (GetValue (Var r_case1)) new_ctx in
					let r_case_stmts3, r_case3 = spec_func_call (StrictEquality (Var r_case2, Var r_test2)) new_ctx in
					let r_case_stmts4, r_stmt = translate_stmt new_ctx [] stmt in 
						[ Sugar (If (equal_bool_expr (Var r_found_a) false, 
							r_case_stmts1 @
              r_case_stmts2 @
              r_case_stmts3 @
							[ Sugar (If (equal_bool_expr (Var r_case3) true, 
									[ Basic (Assignment (mk_assign r_found_a  (Expression (Literal (Bool true))))) ] @							 
				      		r_case_stmts4 @
									[ Basic (Assignment (mk_assign switch_var (Expression (Var r_stmt)))) ],
									[]))], 
							r_case_stmts4)) ]) acumulator.a_cases in 
			  (* *)
			  let b_stmts = List.map (fun (e_case, stmt) ->  
					let r_case_stmts1, r_case1 = translate_exp new_ctx e_case in
					let r_case_stmts2, r_case2 = spec_func_call (GetValue (Var r_case1)) new_ctx in
					let r_case_stmts3, r_case3 = spec_func_call (StrictEquality (Var r_case2, Var r_test2)) new_ctx in
					let r_case_stmts4, r_stmt = translate_stmt new_ctx [] stmt in 
						[ Sugar (If (equal_bool_expr (Var r_found_b) false, 
							r_case_stmts1 @
              r_case_stmts2 @
              r_case_stmts3 @
							[ Sugar (If (equal_bool_expr (Var r_case3) true, 
									[ Basic (Assignment (mk_assign r_found_b  (Expression (Literal (Bool true))))) ] @							 
				      		r_case_stmts4 @
									[ Basic (Assignment (mk_assign switch_var (Expression (Var r_stmt)))) ],
									[]))], 
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
							[ Sugar (If (equal_bool_expr (Var r_found_b) false,
									compiled_default_stmts @
									[ Basic (Assignment (mk_assign switch_var (Expression (Var r_default)))) ] @
									List.flatten simple_b_stmts, 
									[]))]) in
				(* *)				
        let b_stmts = List.flatten b_stmts in
        let b_stmts_if = match b_stmts with
          | [] -> []
          | _ -> [ Sugar (If (equal_bool_expr (Var r_found_a) false,
                     b_stmts, 
                     []));] in	
        let default_stmts_if = match default_stmts with
          | [] -> []
          | _ -> [ Sugar (If (equal_bool_expr (Var r_found_b) false,
                     default_stmts, 
                     [])); ] in
			  (* print_string "stop switching now \n"; *)
				r_test_stmts1 @ 
			  r_test_stmts2 @ 
				[ Basic (Assignment (mk_assign r_found_a (Expression (Literal (Bool false))))) ] @
				List.flatten a_stmts @
				[ Basic (Assignment (mk_assign r_found_b (Expression (Literal (Bool false))))) ] @
        b_stmts_if @
        default_stmts_if @
				[ Label break ], ret_def
		  end
      (* I am not considering those *)  
      
      | Parser_syntax.ForIn _ -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:12.6.4 The for-in Statement.")))
      | Parser_syntax.With _ -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:12.10 With Statemenet.")))
      | Parser_syntax.Debugger -> raise (PulpNotImplemented ((Pretty_print.string_of_exp true exp ^ " REF:12.15 The debugger Statement.")))

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
      [ Sugar (If (equal_empty_expr (Var lvar),
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
  
  make_function_block_with_spec Procedure_User fid pulpe (rthis :: (rscope :: args)) ctx spec

let translate_function_syntax level id e named env main =
  let pulpe = 
    match e.Parser_syntax.exp_stx with
      | Parser_syntax.AnnonymousFun (_, args, fb) -> translate_function fb e.Parser_syntax.exp_annot id main args env None
      | Parser_syntax.NamedFun (_, name, args, fb) -> translate_function fb e.Parser_syntax.exp_annot id main args env named
      | Parser_syntax.Script (_, es) -> translate_function e e.Parser_syntax.exp_annot main main [] env None
      | _ -> raise (Invalid_argument "Should be a function definition here") in
  match level with
    | IVL_buitin_functions -> pulpe
    | IVL_conditionals -> {pulpe with func_body = unfold_spec_functions unfold_spec_function pulpe.func_body}
    | IVL_goto_unfold_functions -> {pulpe with func_body = to_ivl_goto_unfold pulpe.func_body}
    | IVL_goto_with_get_value -> {pulpe with func_body = to_ivl_goto_unfold_leave_gamma pulpe.func_body}
    | IVL_goto -> {pulpe with func_body = to_ivl_goto pulpe.func_body}

let exp_to_pulp_no_builtin level e main ctx_vars = 
  let context = AllFunctions.empty in
  let e = add_codenames main e in
  let all_functions = get_all_functions_with_env_in_fb [] e main in
    
  let all_functions = List.fold_left (fun c (fexpr, fnamed, fenv) -> 
    let fid = get_codename fexpr in
    let fb = translate_function_syntax level fid fexpr fnamed  (fenv @ ctx_vars) main in
    AllFunctions.add fid fb c
   ) context all_functions in
  
  all_functions
  
let exp_to_pulp level e main ctx_vars =
  let context = exp_to_pulp_no_builtin level e main ctx_vars in
  context, (Environment.get_env ()) (* TODO: Singleton *)
