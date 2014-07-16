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

let logic_var v = 
  Logic.Le_Var (AVar v)
  
let logic_string s =
  Logic.pv_le(Logic.Pv_String s)
  
let logic_bool b = 
  Logic.pv_le(Logic.Pv_Bool b)
  
let logic_null = 
  Logic.pv_le(Logic.Pv_Null)
  
let logic_undefined = 
  Logic.pv_le(Logic.Pv_Undefined)

(* ref_type (v, "Member") <=> exists b x, v = b . x *)
(* ref_type (v, "Variable") <=> exists b x, v = b .[v] x *)
let ref_type_pred ref rt =
  let arg1 = logic_var ref in
  let arg2 =  logic_string (string_of_ref_type rt) in
  UDPred ("ref_type", [arg1; arg2])

(* TODO remove *)  
(* ref_field (r, f) <=> exists b, (r = b . f || r = b .[v] f) *)
let ref_field_pred ref f =
  UDPred ("ref_field", [logic_var ref; logic_string f])
  
(* is_a_ref (r) <=> exists b f rt, r = b .[rt] f *)
let is_a_ref_pred ref =
  UDPred ("is_a_ref", [logic_var ref])
  
(* TODO remove *)
(* undef_ref (r) <=> ref_base (r, #undefined) *)
let undef_ref_pred ref =
  UDPred ("undef_ref", [logic_var ref])
  
(* TODO remove*)
(* ref_prim_base (r) <=> exists b, ref_base (r, b) * b #in (#B #union #M #union #N) *)
let ref_prim_base_pred ref =
  UDPred ("ref_prim_base", [logic_var ref])
  
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

type expr_to_fb_return = {
     etf_stmts : statement list;
     etf_lvar : variable;
  }
  
let mk_etf_return stmts lvar = {
     etf_stmts = stmts;
     etf_lvar = lvar;
  }
  
let add_proto obj proto =
  let r1 = mk_assign_fresh_lit (String (string_of_builtin_field FProto)) in
  let r2 = mk_assign_fresh proto in
  let r3 = mk_assign_fresh (Ref (mk_ref obj r1.assign_left MemberReference)) in
  let r4 = Mutation (mk_mutation r3.assign_left r2.assign_left) in
  [Assignment r1; Assignment r2; Assignment r3; r4]
  
let translate_error_throw error throw_var throw_label =
  let r1 = mk_assign_fresh Obj in
  let proto_stmts = add_proto r1.assign_left (Var (string_of_builtin_loc error)) in
  let r2 = mk_assign throw_var (Var r1.assign_left) in
  let r3 = Goto [throw_label] in
  [Assignment r1] @ proto_stmts @ [Assignment r2; r3]
  
let translate_put_value v1 v2 throw_var throw_label =
  let cond1 = Logic.Negation (is_a_ref_pred v1) in
  let gotothrow = translate_error_throw LRError throw_var throw_label in
  let if_not_ref = Sugar (If (cond1, gotothrow, [])) in
  let cond2 = undef_ref_pred v1 in
  let if_undef_ref = Sugar (If (cond2, gotothrow, [])) in
  let cond3 = ref_prim_base_pred v1 in
  let gotothrowtype = translate_error_throw LTError throw_var throw_label in
  let if_prim_ref = Sugar (If (cond3, gotothrowtype, [])) in
  let update = Mutation (mk_mutation v1 v2) in
  let lvar = mk_assign_fresh (Var rempty) in
  mk_etf_return [if_not_ref; if_undef_ref; if_prim_ref; update; Assignment lvar] lvar.assign_left
  
let translate_gamma r ctx =
  let rv = fresh_r () in
  let cond1 = Logic.Negation (is_a_ref_pred r) in
  let assign_rv_r = Assignment (mk_assign rv (Var r)) in
  let if1 = Sugar (If (cond1, [assign_rv_r], [])) in
  let cond2 = undef_ref_pred r in
  let gotothrow1 = translate_error_throw LRError ctx.throw_var ctx.label_throw in 
  let if2 = Sugar (If (cond2, gotothrow1, [])) in
  let cond3 = ref_prim_base_pred r in
  let gotothrow2 = translate_error_throw LNotImplemented ctx.throw_var ctx.label_throw in 
  let if3 = Sugar (If (cond3, gotothrow2, [])) in
  let cond4 = ref_type_pred r VariableReference in
  let assign_rv_lookup = mk_assign rv (Lookup r) in
  let if4 = Sugar (If (cond4, [Assignment assign_rv_lookup], [])) in
  let cond5 = ref_type_pred r MemberReference in
  let base_assign = mk_assign_fresh (Base r) in
  let field_assign = mk_assign_fresh (Field r) in
  let rv_assign_pi = mk_assign rv (BuiltInFunction(Pi (base_assign.assign_left, field_assign.assign_left))) in
  let if5 = Sugar (If (cond5, [Assignment base_assign; Assignment field_assign; Assignment rv_assign_pi], [])) in
  [if1; if2; if3; if4; if5], rv
  
let translate_obj_coercible r ctx =
  let rv = fresh_r () in
  let cond1 = Logic.Eq (logic_var r, logic_null) in
  let gotothrow = translate_error_throw LTError ctx.throw_var ctx.label_throw in
  let if1 = Sugar (If (cond1, gotothrow, [])) in
  let cond2 = Logic.Eq (logic_var r, logic_undefined) in
  let if2 = Sugar (If (cond2, gotothrow, [])) in
  let assign_rv_empty = mk_assign rv (Var rempty) in 
  [if1; if2; Assignment assign_rv_empty], rv
  
let translate_call_construct_start f e1 e2s ctx =
    let r1 = f e1 in
    let r2_stmts, r2 = translate_gamma r1.etf_lvar ctx in 
    let arg_stmts = List.map (fun e ->
        begin
          let re1 = f e in
          let re2_stmts, re2 = translate_gamma re1.etf_lvar ctx in 
          (re2, re1.etf_stmts @ re2_stmts)
        end
     ) e2s in  
    let arg_values, arg_stmts = List.split arg_stmts in
    let arg_stmts = List.flatten arg_stmts in  
    let cond1 = Logic.Negation (type_of_pred r2 Logic.LT_Object) in
    let gotothrow = translate_error_throw LTError ctx.throw_var ctx.label_throw in
    let if1 = Sugar (If (cond1, gotothrow, [])) in
    let fid_ref = mk_assign_fresh (Ref(mk_ref r2 (string_of_builtin_field FId) MemberReference)) in
    let hasfield = mk_assign_fresh (HasField fid_ref.assign_left) in
    let cond2 = Logic.Eq (logic_var hasfield.assign_left, logic_bool false) in
    let if2 = Sugar (If (cond2, gotothrow, [])) in
    (r1.etf_stmts @ r2_stmts @ arg_stmts @ [if1; Assignment fid_ref; Assignment hasfield; if2], r1, r2, arg_values)
    
let translate_call r2 vthis arg_values =
		(*TODO Eval*)
    let cond6 = Logic.NEq (logic_var r2, lb_le (Lb_Loc LEval)) in
		let fid_ref = mk_assign_fresh (Ref (mk_ref r2 (string_of_builtin_field FId) MemberReference)) in
		let fid = mk_assign_fresh (Lookup fid_ref.assign_left) in
		let scope_ref = mk_assign_fresh (Ref (mk_ref r2 (string_of_builtin_field FScope) MemberReference)) in
		let fscope = mk_assign_fresh (Lookup scope_ref.assign_left) in
		let call = mk_assign_fresh (Call (mk_call fid.assign_left fscope.assign_left vthis arg_values)) in
		let if5 = Sugar (If (cond6, [Assignment fid_ref; Assignment fid; Assignment scope_ref; Assignment fscope; Assignment call], [])) in
    (if5, call)
    
let translate_regular_bin_op f op e1 e2 ctx =
  let r1 = f e1 in
  let r2_stmts, r2 = translate_gamma r1.etf_lvar ctx in
  let r3 = f e2 in
  let r4_stmts, r4 = translate_gamma r3.etf_lvar ctx in
  let r5 = mk_assign_fresh (BinOp (r2, tr_bin_op op, r4)) in
  mk_etf_return (r1.etf_stmts @ r2_stmts @ r3.etf_stmts @ r4_stmts @ [Assignment r5]) r5.assign_left
  
let translate_bin_op_logical f e1 e2 bop ctx =
  let op = tr_boolean_op bop in
  let r1 = f e1 in
  let r2_stmts, r2 = translate_gamma r1.etf_lvar ctx in
  let cond = if (op = And) then Logic.IsFalse (logic_var r2) else Logic.IsTrue (logic_var r2) in
  let rv = fresh_r () in
  let assign_rv_r2 = Assignment (mk_assign rv (Var r2)) in
  let r3 = f e2 in
  let r4_stmts, r4 = translate_gamma r3.etf_lvar ctx in
  let assign_rv_op = mk_assign rv (BinOp (r2, Boolean op, r4)) in
  let if1 = Sugar (If (cond, [assign_rv_r2], (r3.etf_stmts) @ r4_stmts @ [Assignment assign_rv_op])) in
  mk_etf_return (r1.etf_stmts @ r2_stmts @ [if1]) rv
  
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
            [Goto [label1; label2]; Label label1; Assume c] @ dt1 @ [Goto [label3]; Label label2; Assume (Logic.Negation c)] @ dt2 @ [Goto [label3]; Label label3]
        end
      | stmt -> [stmt]
  ) stmts)
  
let join_etf_results (results : expr_to_fb_return list) : expr_to_fb_return =
  if List.length results = 0 then raise (Invalid_argument "A list argument for the join_etf_results function should not be empty")
  else
  begin
    let lvar = (List.nth results (List.length results - 1)).etf_lvar in
    List.fold_left (fun joined left_to_join -> 
      mk_etf_return (joined.etf_stmts @ left_to_join.etf_stmts) lvar
    ) (mk_etf_return [] lvar) results
  end
  
let find_var_scope var env =
  try 
  let scope = List.find (fun scope ->
    List.exists (fun v -> v = var) scope.fun_bindings
    ) env in
  scope.func_id
  with
    | Not_found -> unknownscope

let rec exp_to_fb ctx exp : expr_to_fb_return = 
  let mk_result = mk_etf_return in
  let f = exp_to_fb ctx in 
  match exp.Parser_syntax.exp_stx with
      (* Literals *)
      | Parser_syntax.Num n -> 
        begin
          let assign = mk_assign_fresh_lit (Num n) in 
          mk_result [Assignment assign] assign.assign_left
        end
      | Parser_syntax.String s -> 
        begin 
          let assign = mk_assign_fresh_lit (String s) in 
          mk_result [Assignment assign] assign.assign_left
        end
      | Parser_syntax.Null ->
        begin 
          let assign = mk_assign_fresh_lit Null in 
          mk_result [Assignment assign] assign.assign_left
        end
      | Parser_syntax.Bool b -> 
        begin 
          let assign = mk_assign_fresh_lit (Bool b) in 
          mk_result [Assignment assign] assign.assign_left
        end
      | Parser_syntax.This -> 
        begin 
          let assign = mk_assign_fresh (Var rthis) in 
          mk_result [Assignment assign] assign.assign_left
        end
      | Parser_syntax.Var v -> 
        begin 
          let scope = function_scope_name (find_var_scope v ctx.env_vars) in
          let var = mk_assign_fresh_lit (String v) in
          let ref_assign = mk_assign_fresh (Ref (mk_ref scope var.assign_left VariableReference)) in
          mk_result [Assignment var; Assignment ref_assign] ref_assign.assign_left         
        end
      | Parser_syntax.Access (e, v) -> 
        begin
          let r1 = f e in
          let r2_stmts, r2 = translate_gamma r1.etf_lvar ctx in
          let r3 = mk_assign_fresh_lit (Pulp_Syntax.String v) in
          let r4_stmts, r4 = translate_obj_coercible r2 ctx in
          let r5 = mk_assign_fresh (Ref(mk_ref r2 r3.assign_left MemberReference)) in
          mk_etf_return (r1.etf_stmts @ r2_stmts @ [Assignment r3] @ r4_stmts @[Assignment r5]) r5.assign_left;
        end
      | Parser_syntax.CAccess (e1, e2) ->
          let r1 = f e1 in
          let r2_stmts, r2 = translate_gamma r1.etf_lvar ctx in
          let r3 = f e2 in
          let r4_stmts, r4 = translate_gamma r3.etf_lvar ctx in
          let r5_stmts, r5 = translate_obj_coercible r2 ctx in
          let r6 = mk_assign_fresh (Ref(mk_ref r2 r4 MemberReference)) in
          mk_etf_return (r1.etf_stmts @ r2_stmts @ r3.etf_stmts @ r4_stmts @ r5_stmts @ [Assignment r6]) r6.assign_left;
      | Parser_syntax.Script (_, es)
      | Parser_syntax.Block es ->
        let retv = mk_assign_fresh (Var rempty) in
        let mk_if rval oldrval =
          let cond = Logic.Eq (logic_var rval, logic_var rempty) in
          let retv1 = mk_assign_fresh (Var oldrval) in
          (* dynamic SSA *)
          let retv2 = mk_assign retv1.assign_left (Var rval) in 
          let ifstmt = Sugar (If (cond, [Assignment retv1], [Assignment retv2])) in 
          mk_etf_return [ifstmt] retv1.assign_left in
        let skip = mk_etf_return [Assignment retv] retv.assign_left in
        List.fold_left (fun prev current -> 
          let r1 = f current in
          let ifstmt = mk_if r1.etf_lvar prev.etf_lvar in
          join_etf_results [prev; r1; ifstmt]) 
        skip es
      | Parser_syntax.Obj xs ->
        begin
          let r1 = mk_assign_fresh Obj in
          let proto_stmts = add_proto r1.assign_left (Var (PrintLogic.string_of_loc Logic.Lop)) in
          let stmts = List.map (fun (prop_name, prop_type, e) ->
            match prop_type with
              | Parser_syntax.PropbodyVal ->
                begin
                  let r2 = f e in
                  let r3_stmts, r3 = translate_gamma r2.etf_lvar ctx in
                  let r4 = mk_assign_fresh_lit (String (Pretty_print.string_of_propname prop_name)) in
                  let r5 = mk_assign_fresh (Ref(mk_ref r1.assign_left r4.assign_left MemberReference)) in
                  let r6 = Mutation (mk_mutation r5.assign_left r3) in
                  r2.etf_stmts @ r3_stmts @ [Assignment r4; Assignment r5; r6]
                end
              | _ -> raise (PulpNotImplemented ("Getters and Setters are not yet implemented"))
            ) xs in
          let r6 = mk_assign_fresh (Var r1.assign_left) in
          mk_etf_return ([Assignment r1] @ proto_stmts @ (List.flatten stmts) @ [Assignment r6]) r6.assign_left 
        end
      | Parser_syntax.Assign (e1, e2) ->
        begin
          let r1 = f e1 in
          let r2 = f e2 in
          let r3_stmts, r3 = translate_gamma r2.etf_lvar ctx in
          (* TODO: Change logic to have || *)
          let cond1 = ref_type_pred r1.etf_lvar VariableReference in
          let cond2 = ref_field_pred r1.etf_lvar "arguments" in
          let cond3 = ref_field_pred r1.etf_lvar "eval" in
          let cond12 = Logic.Star [cond1; cond2] in
          let cond13 = Logic.Star [cond1; cond3] in
          let gotothrow = translate_error_throw LRError ctx.throw_var ctx.label_throw in
          let if1 = Sugar (If (cond12, gotothrow, [])) in
          let if2 = Sugar (If (cond13, gotothrow, [])) in
          let putvalue = translate_put_value r1.etf_lvar r3 ctx.throw_var ctx.label_throw in
          let r4 = mk_assign_fresh (Var r3) in
          mk_etf_return (r1.etf_stmts @ r2.etf_stmts @ r3_stmts @ [if1; if2] @ putvalue.etf_stmts @ [Assignment r4]) r4.assign_left
        end
      | Parser_syntax.Skip -> 
        let r1 = mk_assign_fresh (Var rempty) in
        mk_etf_return [Assignment r1] r1.assign_left 
      | Parser_syntax.VarDec vars ->
        let result = List.map (fun var ->
          match var with
            | (v, Some exp) -> f ({exp with Parser_syntax.exp_stx = (Parser_syntax.Assign ({exp with Parser_syntax.exp_stx = Parser_syntax.Var v}, exp))})
            | (v, None) -> f ({exp with Parser_syntax.exp_stx = Parser_syntax.Skip})
          ) vars in
        let stmts = (join_etf_results result).etf_stmts in
        let empty = mk_assign_fresh (Var rempty) in
        mk_etf_return (stmts @ [Assignment empty]) empty.assign_left
      | Parser_syntax.AnnonymousFun (_, vs, e) ->
        let fid = get_codename exp in
        let f_obj = mk_assign_fresh Obj in
        let f_obj_proto_stmts = add_proto f_obj.assign_left (Var (PrintLogic.string_of_loc Lfp)) in
        let prototype = mk_assign_fresh Obj in
        let prototype_proto_stmts = add_proto prototype.assign_left (Var (PrintLogic.string_of_loc Lop)) in
        let f_prototype_ref = mk_assign_fresh (Ref (mk_ref f_obj.assign_left (string_of_builtin_field FPrototype) MemberReference)) in
        let f_prototype_update = Mutation (mk_mutation f_prototype_ref.assign_left prototype.assign_left) in
        let scope = mk_assign_fresh Obj in
        let scope_proto_stmts = add_proto scope.assign_left (Literal Null) in
        let env_stmts = Utils.flat_map (fun env -> 
          let env_scope = function_scope_name env.func_id in
          let ref_assign = mk_assign_fresh (Ref (mk_ref scope.assign_left env.func_id MemberReference)) in 
          [Assignment ref_assign; Mutation (mk_mutation ref_assign.assign_left env_scope)]
          ) ctx.env_vars in
        let f_codename_ref = mk_assign_fresh (Ref (mk_ref f_obj.assign_left (string_of_builtin_field FId) MemberReference)) in
        let f_codename_update = Mutation (mk_mutation f_codename_ref.assign_left fid) in
        let f_scope_ref = mk_assign_fresh (Ref (mk_ref f_obj.assign_left (string_of_builtin_field FScope) MemberReference)) in
        let f_scope_update = Mutation (mk_mutation f_scope_ref.assign_left scope.assign_left) in
        let f_assign = mk_assign_fresh (Var f_obj.assign_left) in
        mk_etf_return ([Assignment f_obj] @ f_obj_proto_stmts @ [Assignment prototype] @ prototype_proto_stmts @ 
                       [Assignment f_prototype_ref; f_prototype_update] @ [Assignment scope] @ scope_proto_stmts
                       @ env_stmts @ [Assignment f_codename_ref; f_codename_update; 
                       Assignment f_scope_ref; f_scope_update; Assignment f_assign]) f_assign.assign_left  
      | Parser_syntax.Call (e1, e2s) ->
        let stmts, r1, r2, arg_values = translate_call_construct_start f e1 e2s ctx in
			  let vthis = fresh_r () in
			  let cond3 = Logic.Negation (is_a_ref_pred r1.etf_lvar) in
			  let assign_vthis_und = Assignment (mk_assign vthis (Literal Undefined)) in
			  let if2 = Sugar (If (cond3, [assign_vthis_und], [])) in
			  let cond4 = ref_type_pred r1.etf_lvar VariableReference in
			  let if3 = Sugar (If (cond4, [assign_vthis_und], [])) in
			  let cond5 = ref_type_pred r1.etf_lvar MemberReference in
			  let base_assign = mk_assign_fresh (Base r1.etf_lvar) in
			  let assign_vthis_base = Assignment (mk_assign vthis (Var base_assign.assign_left)) in
			  let if4 = Sugar (If (cond5, [Assignment base_assign; assign_vthis_base], [])) in
			  let if5, call = translate_call r2 vthis arg_values in
			  mk_etf_return (stmts @ [if2; if3; if4; if5]) call.assign_left
        
      | Parser_syntax.New (e1, e2s) ->
        let stmts, r1, r2, arg_values = translate_call_construct_start f e1 e2s ctx in
        let prototype_ref = mk_assign_fresh (Ref (mk_ref r2 (string_of_builtin_field FPrototype) MemberReference)) in
        let prototype = mk_assign_fresh (Lookup prototype_ref.assign_left) in        
			  let vthisproto = fresh_r () in
			  let cond1 = type_of_pred prototype.assign_left Logic.LT_Object in
			  let assign_vthis_r1 = Assignment (mk_assign vthisproto (Var r2)) in
        let assign_vthis_r2 = Assignment (mk_assign vthisproto (Var (PrintLogic.string_of_loc Logic.Lop))) in
			  let if2 = Sugar (If (cond1, [assign_vthis_r1], [assign_vthis_r2])) in
        let vthis = mk_assign_fresh Obj in
        let proto_stmts = add_proto vthis.assign_left (Var vthisproto) in
			  let if3, call = translate_call r2 vthis.assign_left arg_values in
        let rv = fresh_r () in
        let cond2 = type_of_pred call.assign_left Logic.LT_Object in
        let assign_rv_t = Assignment (mk_assign rv (Var call.assign_left)) in
        let assign_rv_f = Assignment (mk_assign rv (Var vthis.assign_left)) in
        let if4 = Sugar (If (cond2, [assign_rv_t], [assign_rv_f])) in      
        mk_etf_return (stmts @ [Assignment prototype_ref; Assignment prototype; if2; Assignment vthis] @ proto_stmts @ [if3; if4]) rv
      | Parser_syntax.Delete e ->
        let r1 = f e in
        let cond1 = Logic.Negation (is_a_ref_pred r1.etf_lvar) in
        let rv = fresh_r () in
        let assign_rv_true = mk_assign rv (Literal (Bool true)) in
        let if_not_ref = Sugar (If (cond1, [Assignment assign_rv_true], [])) in
        let cond2 = undef_ref_pred r1.etf_lvar in
        let gotothrow = translate_error_throw LSError ctx.throw_var ctx.label_throw in
        let if_undef_ref = Sugar (If (cond2, gotothrow, [])) in
        let cond3 = ref_type_pred r1.etf_lvar VariableReference in
        let if_variable_ref = Sugar (If (cond3, gotothrow, [])) in
        let r2 = mk_assign_fresh (HasField r1.etf_lvar) in
        let r3 = mk_assign_fresh (Field r1.etf_lvar) in
        let r4 = mk_assign_fresh (Base r1.etf_lvar) in
        let prototype_ref = mk_assign_fresh (Ref (mk_ref r4.assign_left (string_of_builtin_field FId) MemberReference)) in
        let r5 = mk_assign_fresh (HasField prototype_ref.assign_left) in
        let cond4 = Logic.Eq (logic_var r2.assign_left, logic_bool false) in
        let cond5 = Logic.Star [Logic.Eq (logic_var r3.assign_left, logic_string (string_of_builtin_field FPrototype)); Logic.Eq (logic_var r5.assign_left, logic_bool true)] in
        let gotothrow_type = translate_error_throw LTError ctx.throw_var ctx.label_throw in
        let elsebranch = Sugar (If (cond5, gotothrow_type, [Assignment assign_rv_true])) in
        let if1 = Sugar (If (cond4, [Assignment assign_rv_true], [elsebranch])) in
        mk_etf_return (r1.etf_stmts @ [if_not_ref; if_undef_ref; if_variable_ref; Assignment r2; Assignment r3; Assignment r4; Assignment prototype_ref; Assignment r5; if1]) rv
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
        let r1 = f e1 in
        let r2_stmts, r2 = translate_gamma r1.etf_lvar ctx in
        let condTrue = Logic.IsTrue (logic_var r2) in
        let r3 = f e2 in
        let rv = fresh_r () in
        let assign_rv_r3 = Assignment (mk_assign rv (Var r3.etf_lvar)) in
        let ifTrue = Sugar (If (condTrue, r3.etf_stmts @ [assign_rv_r3], [])) in
        let condFalse = Logic.IsFalse (logic_var r2) in
        let elsebranch = match e3 with
          | Some e3 -> 
            let r4 = f e3 in
            let assign_rv_r4 = Assignment (mk_assign rv (Var r4.etf_lvar)) in
            let ifFalse = Sugar (If (condFalse, r4.etf_stmts @ [assign_rv_r4], [])) in
            [ifFalse]
          | None -> [] in        
        mk_etf_return (r1.etf_stmts @ r2_stmts @ [ifTrue] @ elsebranch) rv
      | Parser_syntax.While (e1, e2) ->
        let rv = fresh_r () in
        let assign_rv_empty = Assignment (mk_assign rv (Var rempty)) in
        let label1 = fresh_r () in
        let r1 = f e1 in
        let r2_stmts, r2 = translate_gamma r1.etf_lvar ctx in
        let condTrue = Logic.IsTrue (logic_var r2) in
        let r3 = f e2 in
        let condNotEmpty = Logic.NEq (logic_var r3.etf_lvar, logic_var rempty) in
        let r4 = mk_assign rv (Var r3.etf_lvar) in
        let ifempty = Sugar (If (condNotEmpty, [Assignment r4], [])) in
        let ifTrue = Sugar (If (condTrue, r3.etf_stmts @ [ifempty; Goto [label1]], [])) in
        mk_etf_return ([assign_rv_empty; Label label1] @ r1.etf_stmts @ r2_stmts @ [ifTrue]) rv
      | Parser_syntax.Return e ->
        let stmts, rv = match e with
          | None -> 
            let und_assign = mk_assign_fresh_lit Undefined in
            [Assignment und_assign], und_assign.assign_left
          | Some e -> 
            let r1 = f e in
            let r2_stmts, r2 = translate_gamma r1.etf_lvar ctx in
            r1.etf_stmts @ r2_stmts, r2
         in
        let assignr = mk_assign ctx.return_var (Var rv) in
        mk_etf_return (stmts @ [Assignment assignr; Goto [ctx.label_return]]) ctx.return_var
        
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
     Assignment (mk_assign (function_scope_name env.func_id) (Ref (mk_ref rscope env.func_id MemberReference))) 
  ) other_env in
  let current_scope_var = function_scope_name fid in
  let current_scope, proto_stmts = 
    if (fid = main_fun_id) then
      (Assignment (mk_assign current_scope_var (Var (PrintLogic.string_of_loc Logic.Lg))),
       add_proto current_scope_var (Var (PrintLogic.string_of_loc Logic.Lop)))
  else 
       (Assignment (mk_assign current_scope_var Obj),
        add_proto current_scope_var (Literal Null)) in
  let init_vars = Utils.flat_map (fun v ->
      let v_assign = mk_assign_fresh_lit (String v) in
      let ref_assign = mk_assign_fresh (Ref (mk_ref current_scope_var v_assign.assign_left VariableReference)) in 
      [Assignment v_assign; Assignment ref_assign; Mutation (mk_mutation ref_assign.assign_left v)]
    ) args in
  (* Assigning undefined to var declarations *)
  let decl_vars = Utils.flat_map (fun v ->
      let v_assign = mk_assign_fresh_lit (String v) in
      let ref_assign = mk_assign_fresh (Ref (mk_ref current_scope_var v_assign.assign_left VariableReference)) in 
      let und_assign = mk_assign_fresh_lit Undefined in
      [Assignment v_assign; Assignment ref_assign; Assignment und_assign; Mutation (mk_mutation ref_assign.assign_left und_assign.assign_left)]
    ) (List.filter (fun v -> not (List.mem v args)) (var_decls fb)) in
  let pulpe = init_e @ [current_scope] @ proto_stmts @ init_vars @ decl_vars @ (exp_to_fb ctx fb).etf_stmts in
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
