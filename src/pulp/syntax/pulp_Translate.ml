open Pulp_Syntax
open Pulp_Syntax_Utils
open Pulp_Syntax_Print
open Logic

exception PulpNotImplemented of string
 
  
let rthis : variable = "rthis"
let rempty : variable = "rempty" (* Using this variable temporarily since logic at the moment does not have value "empty"*)
let rscope : variable = "rscope"
let unknownscope : variable = "unknownscope"

let function_scope_name fid =
  fid^"_scope"

let end_label : label = "theend"

(* Logic -- merge with existing logic or have a new one?? *)
type builtin_loc = 
  | LRError (* Reference Error *)
  | LTError (* Type Error *)
  | LSError (* Syntax Error *)
  | LNotImplemented (* The tool cannot handle this case atm *)

let string_of_builtin_loc l =
  match l with
    | LRError -> "#lrerror"
    | LTError -> "#lterror"
    | LSError -> "#lserror"
    | LNotImplemented -> "#lnotimplemented"

type builtin_field =
  | FProto
  | FId
  | FScope
  | FPrototype

let string_of_builtin_field f =
  match f with
    | FProto -> "#proto"
    | FId -> "#fid"
    | FScope -> "#scope"
    | FPrototype -> "prototype"


let literal_builtin_field f = Literal (String (string_of_builtin_field f))

let logic_var v = Logic.Le_Var (AVar v)
  
let logic_string s = Logic.pv_le (Logic.Pv_String s)
  
let logic_bool b = Logic.pv_le (Logic.Pv_Bool b)
  
let logic_null = Logic.pv_le (Logic.Pv_Null)
  
let logic_undefined = Logic.pv_le (Logic.Pv_Undefined)

let logic_loc l = Logic.lb_le (Lb_Loc l)
  
let logic_eq_undef v = Logic.Eq (logic_var v, logic_undefined)

let logic_eq_null v = Logic.Eq (logic_var v, logic_null)

let logic_eq_bool v b = Logic.Eq (logic_var v, logic_bool b)

let logic_eq_builtin_field v bf = Logic.Eq (logic_var v, logic_string (string_of_builtin_field bf))

(* TODO : have value empty in logic *)
let logic_eq_empty v = Logic.Eq (logic_var v, logic_var rempty)

let logic_eq_loc v l = Logic.Eq (logic_var v, logic_loc l)

let logic_is_false v = Logic.IsFalse (logic_var v)

let logic_is_true v = Logic.IsTrue (logic_var v)

(* ref_type (v, "Member") <=> exists b x, v = b . x *)
(* ref_type (v, "Variable") <=> exists b x, v = b .[v] x *)
let ref_type_pred ref rt =
  let arg1 = logic_var ref in
  let arg2 =  logic_string (string_of_ref_type rt) in
  UDPred ("ref_type", [arg1; arg2])
  
(* is_a_ref (r) <=> exists b f rt, r = b .[rt] f *)
let is_a_ref_pred ref =
  UDPred ("is_a_ref", [logic_var ref])
  
(* type_of_pred (v, t) *)
let type_of_pred v (t : es_lang_type) =
  UDPred ("type_of", [logic_var v; logic_string (PrintLogic.string_of_es_lang_type t)])
  
(* prim (v) <=> type_of (v, #B) || type_of (v, #M) || type_of(v, #N) *)
let prim_pred v =
  UDPred ("prim", [logic_var v])
  
(* End of Logic *)

(* Assignment *)
let mk_assign var exp = { 
    assign_left = var; 
    assign_right = exp
  }

(* Assignment to a fresh variable *)
let mk_assign_fresh exp = mk_assign (fresh_r ()) exp
  
let mk_assign_fresh_lit lit = mk_assign_fresh (Literal lit)

let tr_unary_op op =
  match op with
      | Parser_syntax.Not
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
  Mutation (mk_mutation (Var obj) (literal_builtin_field FProto) proto)
  
let add_proto_var obj proto =
  add_proto obj (Var proto)
  
let add_proto_lvalue obj proto =
  add_proto obj (Literal (String (PrintLogic.string_of_loc proto)))
  
let add_proto_value obj proto =
  add_proto obj (Literal (String (string_of_builtin_loc proto)))
  
let add_proto_null obj =
  add_proto obj (Literal (String (PrintLogic.string_of_loc_b Lb_LocNull)))
  
let translate_error_throw error throw_var throw_label =
  let r1 = mk_assign_fresh Obj in
  [
    Assignment r1; 
    add_proto_value r1.assign_left error; 
    Assignment (mk_assign throw_var (Var r1.assign_left)); 
    Goto [throw_label]
  ]
  
let translate_put_value v1 v2 throw_var throw_label =
  let gotothrow = translate_error_throw LRError throw_var throw_label in
  let base = mk_assign_fresh (Base (Var v1)) in
  let main = Sugar (If (is_a_ref_pred v1,
    [
      Assignment base;
      Sugar (If (logic_eq_undef base.assign_left, 
        gotothrow, 
        [
          Sugar (If (prim_pred base.assign_left, 
            translate_error_throw LTError throw_var throw_label, 
            [Mutation (mk_mutation (Var base.assign_left) (Field (Var v1)) (Var v2))]))
        ]))
    ],
    gotothrow))
  in
  main
  
let translate_gamma r ctx =
  let rv = fresh_r () in
  let base = mk_assign_fresh (Base (Var r)) in
  let field = mk_assign_fresh (Field (Var r)) in
  let assign_rv_lookup = mk_assign rv (Lookup (Var base.assign_left, Var field.assign_left)) in
  let rv_assign_pi = mk_assign rv (Pi (Var base.assign_left, Var field.assign_left)) in  
  let main = Sugar (If (is_a_ref_pred r,
    [
      Assignment base;
      Sugar (If (logic_eq_undef base.assign_left,
        translate_error_throw LRError ctx.throw_var ctx.label_throw,
        [
          Sugar (If (prim_pred base.assign_left,
            translate_error_throw LNotImplemented ctx.throw_var ctx.label_throw,
            [
              Assignment field;
              Sugar (If (Logic.Star[ref_type_pred r VariableReference; Negation (logic_eq_loc base.assign_left Lg)],
                [ Assignment assign_rv_lookup ],
                [ Assignment rv_assign_pi ]))
            ]))
        ]))
    ],
    [ Assignment (mk_assign rv (Var r)) ]))
  in
  [main], rv

let translate_obj_coercible r ctx =
  let rv = fresh_r () in
  let gotothrow = translate_error_throw LTError ctx.throw_var ctx.label_throw in 
  [
    Sugar (If (logic_eq_null r, gotothrow, [])); 
    Sugar (If (logic_eq_undef r, gotothrow, [])); 
    Assignment (mk_assign rv (Literal Empty))
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
        Sugar (If (type_of_pred r2 Logic.LT_Object, [], gotothrow)); 
        Assignment hasfield; 
        Sugar (If (logic_eq_bool hasfield.assign_left false, gotothrow, []))
      ], r1, r2, arg_values)
    
let translate_call r2 vthis arg_values ctx =
		let fid = mk_assign_fresh (Lookup (Var r2, literal_builtin_field FId)) in
		let fscope = mk_assign_fresh (Lookup (Var r2, literal_builtin_field FScope)) in
		let call = mk_assign_fresh (Call (mk_call (Var fid.assign_left) (Var fscope.assign_left) (Var vthis) arg_values)) in
    (Sugar (If (logic_eq_loc r2 LEval,
        (*TODO Eval*)
        translate_error_throw LNotImplemented ctx.throw_var ctx.label_throw, 
        [
          Assignment fid; 
          Assignment fscope; 
          Assignment call
     ])), call)
    
let translate_regular_bin_op f op e1 e2 ctx =
  let r1_stmts, r1 = f e1 in
  let r2_stmts, r2 = translate_gamma r1 ctx in
  let r3_stmts, r3 = f e2 in
  let r4_stmts, r4 = translate_gamma r3 ctx in
  let r5 = mk_assign_fresh (BinOp (Var r2, tr_bin_op op, Var r4)) in
    r1_stmts @ 
    r2_stmts @ 
    r3_stmts @ 
    r4_stmts @ 
    [Assignment r5],
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
      Sugar (If ((if (op = And) then (logic_is_false r2) else (logic_is_true r2)), 
        [Assignment (mk_assign rv (Var r2))], 
	      (r3_stmts) @ 
	      r4_stmts @ 
	      [Assignment (mk_assign rv (BinOp (Var r2, Boolean op, Var r4)))]))
    ], rv
  
let rec desugar stmts = 
  List.flatten (List.map (fun stmt ->
    match stmt with
      | Sugar st -> 
        begin match st with
          | If (c, t1, t2) -> 
            let label1 = fresh_r () in
            let label2 = fresh_r () in
            let label3 = fresh_r () in
            let dt1 = desugar t1 in
            let dt2 = desugar t2 in
            [
              Goto [label1; label2]; 
              Label label1; 
              Assume c
            ] @ 
            dt1 @ 
            [
              Goto [label3]; 
              Label label2; 
              Assume (Logic.Negation c)
            ] @ 
            dt2 @ 
            [
              Goto [label3]; 
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
  scope.func_id
  with
    | Not_found -> unknownscope

let rec exp_to_fb ctx exp : statement list * variable = 
  let f = exp_to_fb ctx in 
  match exp.Parser_syntax.exp_stx with
      (* Literals *)
      | Parser_syntax.Num n -> 
        begin
          let assign = mk_assign_fresh_lit (Num n) in 
          [Assignment assign], assign.assign_left
        end
      | Parser_syntax.String s -> 
        begin 
          let assign = mk_assign_fresh_lit (String s) in 
          [Assignment assign], assign.assign_left
        end
      | Parser_syntax.Null ->
        begin 
          let assign = mk_assign_fresh_lit Null in 
          [Assignment assign], assign.assign_left
        end
      | Parser_syntax.Bool b -> 
        begin 
          let assign = mk_assign_fresh_lit (Bool b) in 
          [Assignment assign], assign.assign_left
        end
      | Parser_syntax.This -> 
        begin 
          let assign = mk_assign_fresh (Var rthis) in 
          [Assignment assign], assign.assign_left
        end
      | Parser_syntax.Var v -> 
        begin 
          let scope = function_scope_name (find_var_scope v ctx.env_vars) in
          let ref_assign = mk_assign_fresh (Ref (Var scope, Literal (String v) , VariableReference)) in
          [Assignment ref_assign], ref_assign.assign_left         
        end
      | Parser_syntax.Access (e, v) -> 
        begin
          let r1_stmts, r1 = f e in
          let r2_stmts, r2 = translate_gamma r1 ctx in
          let r4_stmts, r4 = translate_obj_coercible r2 ctx in
          let r5 = mk_assign_fresh (Ref (Var r2, Literal (String v), MemberReference)) in
            r1_stmts @ 
            r2_stmts @ 
            r4_stmts @
            [Assignment r5], r5.assign_left;
        end
      | Parser_syntax.CAccess (e1, e2) ->
          let r1_stmts, r1 = f e1 in
          let r2_stmts, r2 = translate_gamma r1 ctx in
          let r3_stmts, r3 = f e2 in
          let r4_stmts, r4 = translate_gamma r3 ctx in
          let r5_stmts, r5 = translate_obj_coercible r2 ctx in
          let r6 = mk_assign_fresh (Ref (Var r2, Var r4, MemberReference)) in
            r1_stmts @ 
            r2_stmts @ 
            r3_stmts @ 
            r4_stmts @ 
            r5_stmts @ 
            [Assignment r6], r6.assign_left;
      | Parser_syntax.Script (_, es)
      | Parser_syntax.Block es ->
        let mk_if rval oldrval =
          let retv = fresh_r () in 
            [
              (* DSA *) 
              Sugar (If (logic_eq_empty rval, 
                [
                  Assignment (mk_assign retv (Var oldrval))
                ], 
                [
                  Assignment (mk_assign retv (Var rval))
                ]))
            ], retv in
         
        let retv = mk_assign_fresh (Literal Empty) in
        
        List.fold_left (fun (prev_stmts, prev) current -> 
          let r1_stmts, r1 = f current in
          let if_stmts, ifv = mk_if r1 prev in
          (prev_stmts @ r1_stmts @ if_stmts, ifv)) 
        ([Assignment retv], retv.assign_left) es
        
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
                  [Mutation (mk_mutation (Var r1.assign_left) (Literal (String (Pretty_print.string_of_propname prop_name))) (Var r3))] 
                   
                end
              | _ -> raise (PulpNotImplemented ("Getters and Setters are not yet implemented"))
            ) xs in
                           
            [
              Assignment r1;
              add_proto_lvalue r1.assign_left Logic.Lop
            ] @ 
            (List.flatten stmts), r1.assign_left
        end
        
      | Parser_syntax.Assign (e1, e2) ->
        begin
          let r1_stmts, r1 = f e1 in
          let r2_stmts, r2 = f e2 in
          let r3_stmts, r3 = translate_gamma r2 ctx in
          let r4 = mk_assign_fresh (Field (Var r1)) in
          let gotothrow = translate_error_throw LRError ctx.throw_var ctx.label_throw in
          
            r1_stmts @
            r2_stmts @
            r3_stmts @
            [
              Sugar (If (ref_type_pred r1 VariableReference, 
		            [
		              Assignment r4;
		               (* TODO: Change logic to have || *)
		              Sugar (If (Logic.Eq (logic_var r4.assign_left, logic_string "arguments"), gotothrow, []));
		              Sugar (If (Logic.Eq (logic_var r4.assign_left, logic_string "eval"), gotothrow, []));
		            ], 
		            []))
            ] @
            [translate_put_value r1 r3 ctx.throw_var ctx.label_throw], r3
        end
        
      | Parser_syntax.Skip -> 
        let r1 = mk_assign_fresh (Literal Empty) in
        [Assignment r1], r1.assign_left 
        
      | Parser_syntax.VarDec vars ->
        let result = List.map (fun var ->
          match var with
            | (v, Some exp) -> f ({exp with Parser_syntax.exp_stx = (Parser_syntax.Assign ({exp with Parser_syntax.exp_stx = Parser_syntax.Var v}, exp))})
            | (v, None) -> f ({exp with Parser_syntax.exp_stx = Parser_syntax.Skip})
          ) vars in
        let stmts, _ = List.split result in
        let empty = mk_assign_fresh (Literal Empty) in
        (List.flatten stmts) @ [Assignment empty], empty.assign_left
        
      | Parser_syntax.AnnonymousFun (_, vs, e) ->
        let fid = get_codename exp in
        let f_obj = mk_assign_fresh Obj in
        let prototype = mk_assign_fresh Obj in
        let scope = mk_assign_fresh Obj in
        let env_stmts = Utils.flat_map (fun env -> 
          [
            Mutation (mk_mutation (Var scope.assign_left) (Literal (String env.func_id)) (Var (function_scope_name env.func_id)))
          ]) ctx.env_vars in
          [
            Assignment f_obj;
            add_proto_lvalue f_obj.assign_left Lfp;
            Assignment prototype; 
            add_proto_lvalue prototype.assign_left Lop; 
            Mutation (mk_mutation (Var f_obj.assign_left) (literal_builtin_field FPrototype) (Var prototype.assign_left));
            Assignment scope;
            add_proto_null scope.assign_left
          ] @ 
          env_stmts @ 
          [
            Mutation (mk_mutation (Var f_obj.assign_left) (literal_builtin_field FId) (Literal (String fid))); 
            Mutation (mk_mutation (Var f_obj.assign_left) (literal_builtin_field FScope) (Var scope.assign_left)); 
          ], f_obj.assign_left  
                      
      | Parser_syntax.Call (e1, e2s) ->
        let stmts, r1, r2, arg_values = translate_call_construct_start f e1 e2s ctx in
			  let vthis = fresh_r () in
			  let assign_vthis_und = Assignment (mk_assign vthis (Literal Undefined)) in
			  let if5, call = translate_call r2 vthis arg_values ctx in
          stmts @ 
          [
            Sugar (If (is_a_ref_pred r1, 
                [
                  Sugar (If (ref_type_pred r1 VariableReference, 
                    [assign_vthis_und], 
                    [
                      Assignment (mk_assign vthis (Base (Var r1)))
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
            Assignment prototype; 
            Sugar (If (type_of_pred prototype.assign_left Logic.LT_Object, 
                [Assignment (mk_assign vthisproto (Var r2))], 
                [Assignment (mk_assign vthisproto (Var (PrintLogic.string_of_loc Logic.Lop)))])); 
            Assignment vthis;
            add_proto_var vthis.assign_left vthisproto;
            if3; 
            Sugar (If (type_of_pred call.assign_left Logic.LT_Object, 
                [Assignment (mk_assign rv (Var call.assign_left))], 
                [Assignment (mk_assign rv (Var vthis.assign_left))]))
          ], rv
        
      | Parser_syntax.Delete e ->
        let r1_stmts, r1 = f e in
        let rv = fresh_r () in
        let assign_rv_true = mk_assign rv (Literal (Bool true)) in
        let r4 = mk_assign_fresh (Base (Var r1)) in 
        let gotothrow = translate_error_throw LSError ctx.throw_var ctx.label_throw in
        let r3 = mk_assign_fresh (Field (Var r1)) in      
        let r2 = mk_assign_fresh (HasField (Var r4.assign_left, Var r3.assign_left)) in
        (* TODO : Changes when we add attributes *)
        let r5 = mk_assign_fresh (HasField (Var r4.assign_left, literal_builtin_field FId)) in
          r1_stmts @ 
          [
            Sugar (If (is_a_ref_pred r1, 
                [ Assignment r4;
			            Sugar (If (logic_eq_undef r4.assign_left, 
                    gotothrow, 
                    [])); 
			            Sugar (If (ref_type_pred r1 VariableReference, 
                    gotothrow, 
                    [])); 
			            Assignment r3;  
			            Assignment r2; 
			            Sugar (If (logic_eq_bool r2.assign_left false, 
                    [Assignment assign_rv_true], 
                    [
                      Assignment r5; 
                      Sugar (If (Logic.Star [logic_eq_builtin_field r3.assign_left FPrototype; logic_eq_bool r5.assign_left true], 
                        translate_error_throw LTError ctx.throw_var ctx.label_throw, 
                        [Assignment assign_rv_true]))
                    ]))
                ], 
                [Assignment assign_rv_true])); 
          ], rv
          
      | Parser_syntax.BinOp (e1, op, e2) ->
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
            [Assignment (mk_assign rv (Var r4))]
          | None -> [] in      
          r1_stmts @ 
          r2_stmts @ 
          [ 
            Sugar (If (logic_is_true r2, 
                r3_stmts @ 
                [Assignment (mk_assign rv (Var r3))], 
                elsebranch))
          ], rv
        
      | Parser_syntax.While (e1, e2) ->
        let rv = fresh_r () in
        let assign_rv_empty = Assignment (mk_assign rv (Literal Empty)) in
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
            Sugar (If (logic_is_true r2, 
                r3_stmts @ 
                [ 
                  Sugar (If (logic_eq_empty r3, 
                    [], 
                    [Assignment (mk_assign rv (Var r3))])); 
                  Goto [label1]
                ], 
                
                []))
          ], rv
        
      | Parser_syntax.Return e ->
        let stmts, rv = match e with
          | None -> 
            let und_assign = mk_assign_fresh_lit Undefined in
            [Assignment und_assign], und_assign.assign_left
          | Some e -> 
            let r1_stmts, r1 = f e in
            let r2_stmts, r2 = translate_gamma r1 ctx in
            r1_stmts @ r2_stmts, r2
         in
        let assignr = mk_assign ctx.return_var (Var rv) in
          stmts @ 
          [
            Assignment assignr; 
            Goto [ctx.label_return]
          ], ctx.return_var
        
      | Parser_syntax.NamedFun _ (*(_, n, vs, e)*)

      | Parser_syntax.RegExp _
      | Parser_syntax.Unary_op _ 
      | Parser_syntax.AssignOp _
      | Parser_syntax.Comma _
      | Parser_syntax.Array _
      | Parser_syntax.ConditionalOp _
      | Parser_syntax.Break _
      | Parser_syntax.Continue _
      | Parser_syntax.Debugger
      | Parser_syntax.Throw _
      | Parser_syntax.Label _
      | Parser_syntax.DoWhile _
      | Parser_syntax.With _
      | Parser_syntax.Try _
      | Parser_syntax.For _
      | Parser_syntax.ForIn _
      | Parser_syntax.Switch _
        -> raise (PulpNotImplemented (Pretty_print.string_of_exp true exp))
        
let translate_function fb fid args env =
  let ctx = create_ctx env in
  let other_env = match ctx.env_vars with
    | current :: others -> others
    | [] -> raise (Invalid_argument "Should be a function environment here") in
    
  let init_e = List.map (fun env -> 
     Assignment (mk_assign (function_scope_name env.func_id) (Ref (Var rscope, Literal (String env.func_id), MemberReference))) 
  ) other_env in
  
  let current_scope_var = function_scope_name fid in
  
  let current_scope, proto_stmt = 
    if (fid = main_fun_id) then
      (Assignment (mk_assign current_scope_var (Var (PrintLogic.string_of_loc Logic.Lg))),
       add_proto_lvalue current_scope_var Lop)
  else 
       (Assignment (mk_assign current_scope_var Obj),
        add_proto_null current_scope_var) in
        
  let init_vars = Utils.flat_map (fun v ->
      [
        Mutation (mk_mutation (Var current_scope_var) (Literal (String v)) (Var v))
      ]
    ) args in
    
  (* Assigning undefined to var declarations *)
  let decl_vars = Utils.flat_map (fun v ->
      [
        Mutation (mk_mutation (Var current_scope_var) (Literal (String v)) (Literal Undefined))
      ]
    ) (List.filter (fun v -> not (List.mem v args)) (var_decls fb)) in
    
  let pulp_fb, _ = exp_to_fb ctx fb in
    
  let pulpe = 
    init_e @ 
    [current_scope; proto_stmt] @  
    init_vars @ 
    decl_vars @ 
    pulp_fb in
  
  let desugared_pulpe = desugar pulpe in
  
  make_function_block fid desugared_pulpe (rthis :: (rscope :: args)) ctx

let translate_function_syntax id e env =
    match e.Parser_syntax.exp_stx with
      | Parser_syntax.AnnonymousFun (_, args, fb) -> translate_function fb id args env
      | Parser_syntax.NamedFun (_, name, args, fb) -> translate_function fb id args env
      | Parser_syntax.Script (_, es) -> translate_function e main_fun_id [] env
      | _ -> raise (Invalid_argument "Should be a function definition here")

let exp_to_pulp e =
  let context = AllFunctions.empty in
  let e = add_codenames e in
  let all_functions = get_all_functions_with_env [] e in
    
  let context = List.fold_left (fun c (fexpr, fenv) -> 
    let fid = get_codename fexpr in
    let fb = translate_function_syntax fid fexpr fenv in
    AllFunctions.add fid fb c
   ) context all_functions in
  context
