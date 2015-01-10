open Pulp_Syntax
open Pulp_Syntax_Utils
open Pulp_Syntax_Print

exception PulpNotImplemented of string

type translation_level =
  | IVL_buitin_functions
  | IVL_conditionals
  | IVL_goto
 
  
let rthis : variable = "rthis"
let rscope : variable = "rscope"

let function_scope_name fid =
  fid^"_scope"
  
let unknownscope : string = "UNKNOWN_SCOPE"

let end_label : label = "theend"

let literal_builtin_field f = Literal (String (string_of_builtin_field f))

let is_ref_inner ref rt =
  IsTypeOf (Var ref, ReferenceType rt)
  
let is_oref_expr ref = is_ref_inner ref (Some MemberReference)
let is_vref_expr ref = is_ref_inner ref (Some VariableReference)
let is_ref_expr ref = is_ref_inner ref None
let is_obj_var v = IsTypeOf (Var v, ObjectType)

let or_expr e1 e2 = BinOp (e1, Boolean Or, e2)
let and_expr e1 e2 = BinOp (e1, Boolean And, e2)
let not_expr e1 = UnaryOp (Not, e1)
let equal_expr v e2 = BinOp (Var v, Comparison Equal, e2)
  
let istypeof_prim_expr v =
  or_expr 
  (IsTypeOf (Var v, BooleanType))
  (or_expr 
    (IsTypeOf (Var v, NumberType))
    (IsTypeOf (Var v, StringType)))
    
let equal_lit_expr v lit = equal_expr v (Literal lit)
let equal_undef_expr v = equal_lit_expr v Undefined
let equal_null_expr v = equal_lit_expr v Null
let equal_empty_expr v = equal_lit_expr v Empty
let equal_bool_expr v b = equal_lit_expr v (Bool b)
let equal_loc_expr v l = equal_lit_expr v (LLoc l)
let equal_string_expr v s = equal_lit_expr v (String s)
let equal_int_expr v n = equal_lit_expr v (Num (float_of_int n))

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
      | Parser_syntax.TypeOf 
      | Parser_syntax.Positive
      | Parser_syntax.Negative
      | Parser_syntax.Pre_Decr
      | Parser_syntax.Post_Decr
      | Parser_syntax.Pre_Incr
      | Parser_syntax.Post_Incr
      | Parser_syntax.Bitnot
      | Parser_syntax.Void -> raise (PulpNotImplemented (Pretty_print.string_of_unary_op op))

let tr_arith_op op =
  begin match op with
      | Parser_syntax.Plus -> Plus
      | Parser_syntax.Minus -> Minus
      | Parser_syntax.Times -> Times
      | Parser_syntax.Div -> Div
      | Parser_syntax.Mod
      | Parser_syntax.Ursh 
      | Parser_syntax.Lsh 
      | Parser_syntax.Rsh
      | Parser_syntax.Bitand
      | Parser_syntax.Bitor
      | Parser_syntax.Bitxor -> raise (PulpNotImplemented (Pretty_print.string_of_arith_op op))
  end
  
let tr_comparison_op op =
  begin match op with
    | Parser_syntax.Equal -> Equal
    | Parser_syntax.NotEqual 
    | Parser_syntax.TripleEqual 
    | Parser_syntax.NotTripleEqual 
    | Parser_syntax.Lt 
    | Parser_syntax.Le 
    | Parser_syntax.Gt 
    | Parser_syntax.Ge 
    | Parser_syntax.In 
    | Parser_syntax.InstanceOf -> raise (PulpNotImplemented (Pretty_print.string_of_comparison_op op))
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
  let rv_assign_pi = mk_assign rv (Pi (Var base.assign_left, Var field.assign_left)) in  
  let main = Sugar (If (is_ref_expr r,
    [
      Basic (Assignment base);
      Sugar (If (or_expr (equal_undef_expr base.assign_left) (equal_string_expr base.assign_left unknownscope),
        translate_error_throw LRError ctx.throw_var ctx.label_throw,
        [
          Sugar (If (istypeof_prim_expr base.assign_left,
            translate_error_throw LNotImplemented ctx.throw_var ctx.label_throw,
            [
              Basic (Assignment field);
              Sugar (If (and_expr (is_vref_expr r) (not_expr (equal_loc_expr base.assign_left Lg)),
                [ Basic (Assignment assign_rv_lookup) ],
                [ Basic (Assignment rv_assign_pi) ]))
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
		let call = mk_assign_fresh (Call (mk_call (Var fid.assign_left) (Var fscope.assign_left) (Var vthis) arg_values)) in
    (Sugar (If (equal_loc_expr r2 LEval,
        (*TODO Eval*)
        translate_error_throw LNotImplemented ctx.throw_var ctx.label_throw, 
        [
          Basic (Assignment fid); 
          Basic (Assignment fscope); 
          Basic (Assignment call)
     ])), call)
    
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
  
let translate_bin_op_logical f e1 e2 bop ctx =
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
    | Not_found -> Literal (String unknownscope)

let rec exp_to_fb ctx exp : statement list * variable = 
  let f = exp_to_fb ctx in 
  match exp.Parser_syntax.exp_stx with
      (* Literals *)
      | Parser_syntax.Num n -> 
        begin
          let assign = mk_assign_fresh_lit (Num n) in 
          [Basic (Assignment assign)], assign.assign_left
        end
      | Parser_syntax.String s -> 
        begin 
          let assign = mk_assign_fresh_lit (String s) in 
          [Basic (Assignment assign)], assign.assign_left
        end
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
      | Parser_syntax.Access (e, v) -> 
        begin
          let r1_stmts, r1 = f e in
          let r2_stmts, r2 = translate_gamma r1 ctx in
          let r4_stmts, r4 = translate_obj_coercible r2 ctx in
          let r5 = mk_assign_fresh_e (Ref (Var r2, Literal (String v), MemberReference)) in
            r1_stmts @ 
            r2_stmts @ 
            r4_stmts @
            [Basic (Assignment r5)], r5.assign_left;
        end
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
            [Basic (Assignment r6)], r6.assign_left;
      | Parser_syntax.Script (_, es)
      | Parser_syntax.Block es ->
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
              | _ -> raise (PulpNotImplemented ("Getters and Setters are not yet implemented"))
            ) xs in
                           
            [
              Basic (Assignment r1);
              add_proto_value r1.assign_left Lop
            ] @ 
            (List.flatten stmts), r1.assign_left
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
        
      | Parser_syntax.Skip -> 
        let r1 = mk_assign_fresh_lit Empty in
        [Basic (Assignment r1)], r1.assign_left 
        
      | Parser_syntax.VarDec vars ->
        let result = List.map (fun var ->
          match var with
            | (v, Some exp) -> f ({exp with Parser_syntax.exp_stx = (Parser_syntax.Assign ({exp with Parser_syntax.exp_stx = Parser_syntax.Var v}, exp))})
            | (v, None) -> f ({exp with Parser_syntax.exp_stx = Parser_syntax.Skip})
          ) vars in
        let stmts, _ = List.split result in
        let empty = mk_assign_fresh_lit Empty in
        (List.flatten stmts) @ [Basic (Assignment empty)], empty.assign_left
        
      | Parser_syntax.AnnonymousFun (_, vs, e) ->
        let fid = get_codename exp in
        let f_obj = mk_assign_fresh Obj in
        let prototype = mk_assign_fresh Obj in
        let scope = mk_assign_fresh Obj in
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
          env_stmts @ 
          [
            Basic (Mutation (mk_mutation (Var f_obj.assign_left) (literal_builtin_field FId) (Literal (String fid)))); 
            Basic (Mutation (mk_mutation (Var f_obj.assign_left) (literal_builtin_field FScope) (Var scope.assign_left))); 
          ], f_obj.assign_left  
                      
      | Parser_syntax.Call (e1, e2s) ->
        let stmts, r1, r2, arg_values = translate_call_construct_start f e1 e2s ctx in
			  let vthis = fresh_r () in
			  let assign_vthis_und = Basic (Assignment (mk_assign vthis (Expression (Literal Undefined)))) in
			  let if5, call = translate_call r2 vthis arg_values ctx in
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
                [assign_vthis_und])); 
            if5
          ], call.assign_left
        
      | Parser_syntax.New (e1, e2s) ->
        let stmts, r1, r2, arg_values = translate_call_construct_start f e1 e2s ctx in
        let prototype = mk_assign_fresh (Lookup (Var r2, literal_builtin_field FPrototype)) in        
			  let vthisproto = fresh_r () in
        let vthis = mk_assign_fresh Obj in
			  let if3, call = translate_call r2 vthis.assign_left arg_values ctx in
        let rv = fresh_r () in  
          stmts @ 
          [
            Basic (Assignment prototype); 
            Sugar (If (is_obj_var prototype.assign_left, 
                [Basic (Assignment (mk_assign vthisproto (Expression (Var prototype.assign_left))))], 
                [Basic (Assignment (mk_assign vthisproto (Expression (Literal (LLoc Lop)))))])); 
            Basic (Assignment vthis);
            add_proto_var vthis.assign_left vthisproto;
            if3; 
            Sugar (If (is_obj_var call.assign_left, 
                [Basic (Assignment (mk_assign rv (Expression (Var call.assign_left))))], 
                [Basic (Assignment (mk_assign rv (Expression (Var vthis.assign_left))))]))
          ], rv
        
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
              | _ -> raise (PulpNotImplemented (Pretty_print.string_of_exp true exp))
            end
          | Parser_syntax.Arith aop -> 
            begin match aop with
              | Parser_syntax.Plus
						  | Parser_syntax.Minus
						  | Parser_syntax.Times
						  | Parser_syntax.Div -> translate_regular_bin_op f op e1 e2 ctx
						  | _ -> raise (PulpNotImplemented (Pretty_print.string_of_exp true exp))
            end
          | Parser_syntax.Boolean bop -> 
            begin match bop with
              | Parser_syntax.And -> translate_bin_op_logical f e1 e2 bop ctx
              | Parser_syntax.Or -> translate_bin_op_logical f e1 e2 bop ctx
            end
        end
        
      | Parser_syntax.If (e1, e2, e3) ->
        let r1_stmts, r1 = f e1 in
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
        let rv = fresh_r () in
        let assign_rv_empty = Basic (Assignment (mk_assign rv (Expression (Literal Empty)))) in
        let label1 = fresh_r () in
        let r1_stmts, r1 = f e1 in
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
        
      | Parser_syntax.Return e ->
        let stmts, rv = match e with
          | None -> 
            let und_assign = mk_assign_fresh_lit Undefined in
            [Basic (Assignment und_assign)], und_assign.assign_left
          | Some e -> 
            let r1_stmts, r1 = f e in
            let r2_stmts, r2 = translate_gamma r1 ctx in
            r1_stmts @ r2_stmts, r2
         in
        let assignr = mk_assign ctx.return_var (Expression (Var rv)) in
          stmts @ 
          [
            Basic (Assignment assignr); 
            Goto ctx.label_return
          ], ctx.return_var
          
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
          | _ -> raise (PulpNotImplemented (Pretty_print.string_of_exp true exp))
        end
        
      (* Next TODO *)  
      | Parser_syntax.Throw _
      | Parser_syntax.Try _
      | Parser_syntax.NamedFun _ (*(_, n, vs, e)*)
        
      (* Should not change IVL too much *)
      | Parser_syntax.AssignOp _
      | Parser_syntax.Comma _
      | Parser_syntax.Array _
      
      | Parser_syntax.ConditionalOp _
      | Parser_syntax.DoWhile _
      | Parser_syntax.For _
      | Parser_syntax.Switch _
      
      | Parser_syntax.Label _
      | Parser_syntax.Break _
      | Parser_syntax.Continue _

      (* I am not considering those *)  
      | Parser_syntax.RegExp _ 
      | Parser_syntax.ForIn _
      | Parser_syntax.Debugger
      | Parser_syntax.With _
        -> raise (PulpNotImplemented (Pretty_print.string_of_exp true exp))
        
let translate_function fb fid args env =
  let ctx = create_ctx env in
  let other_env = match ctx.env_vars with
    | current :: others -> others
    | [] -> raise (Invalid_argument "Should be a function environment here") in
    
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
    
  (* Assigning undefined to var declarations *)
  let decl_vars = Utils.flat_map (fun v ->
      [
        Basic (Mutation (mk_mutation (Var current_scope_var) (Literal (String v)) (Literal Undefined)))
      ]
    ) (List.filter (fun v -> not (List.mem v args)) (var_decls fb)) in
    
  let pulp_fb, lvar = exp_to_fb ctx fb in
  
  let end_stmts =
    if (fid = main_fun_id) then
      let gamma_stmts, gamma_lvar = translate_gamma lvar ctx in 
      gamma_stmts @ [Basic (Assignment (mk_assign ctx.return_var (Expression (Var gamma_lvar))))]
    else
      [Basic (Assignment (mk_assign ctx.return_var (Expression (Literal Empty))))] in
    
  let pulpe = 
    init_e @ 
    current_scope_stmts @  
    init_vars @ 
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

let translate_function_syntax level id e env =
  let pulpe = 
    match e.Parser_syntax.exp_stx with
      | Parser_syntax.AnnonymousFun (_, args, fb) -> translate_function fb id args env
      | Parser_syntax.NamedFun (_, name, args, fb) -> translate_function fb id args env
      | Parser_syntax.Script (_, es) -> translate_function e main_fun_id [] env
      | _ -> raise (Invalid_argument "Should be a function definition here") in
  match level with
    | IVL_buitin_functions -> raise (Utils.InvalidArgument ("pulp_Translate", "builtin_functions level not implemented yet"))
    | IVL_conditionals -> pulpe
    | IVL_goto -> {pulpe with func_body = to_ivl_goto pulpe.func_body}

let exp_to_pulp level e =
  let context = AllFunctions.empty in
  let e = add_codenames e in
  let all_functions = get_all_functions_with_env [] e in
    
  let context = List.fold_left (fun c (fexpr, fenv) -> 
    let fid = get_codename fexpr in
    let fb = translate_function_syntax level fid fexpr fenv in
    AllFunctions.add fid fb c
   ) context all_functions in
  context
