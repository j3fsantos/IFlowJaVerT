open Pulp_Syntax
open Pulp_Syntax_Utils
open Pulp_Syntax_Print
open Logic

exception PulpNotImplemented of string

let fresh_variable =
  let counter = ref 0 in
  let rec f name =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f
  
let fresh_r () : variable =
  fresh_variable "r"
  
type field = string
  
let rthis : variable = "rthis"
let rempty : variable = "rempty" (* Using this variable temporarily since logic at the moment does not have value "empty"*)
let rscope : variable = "rscope"
let unknownscope : variable = "unknownscope"

let field_fid : field = "#fid"
let field_scope : field = "#scope"

let function_scope_name fid =
  fid^"_scope"

let end_label : label = "theend"

(* Logic -- merge with existing logic or have a new one?? *)
type builtin_loc = 
  | LRError (* Reference Error *)
  | LTError (* Type Error *)
  | LSError (* Syntax Error *)

let string_of_builtin_loc l =
  match l with
    | LRError -> "#lrerror"
    | LTError -> "#lterror"
    | LSError -> "#lserror"

type builtin_field =
  | Proto

let string_of_builtin_field f =
  match f with
    | Proto -> "#proto"

let logic_var v = 
  Logic.Le_Var (AVar v)
  
let logic_string s =
  Logic.pv_le(Logic.Pv_String s)
  
let logic_bool b = 
  Logic.pv_le(Logic.Pv_Bool b)

(* ref_type (v, "Member") <=> exists b x, v = b . x *)
(* ref_type (v, "Variable") <=> exists b x, v = b .[v] x *)
let ref_type_pred ref rt =
  let arg1 = logic_var ref in
  let arg2 =  logic_string (string_of_ref_type rt) in
  UDPred ("ref_type", [arg1; arg2])
  
(* ref_field (r, f) <=> exists b, (r = b . f || r = b .[v] f) *)
let ref_field_pred ref f =
  UDPred ("ref_field", [logic_var ref; logic_string f])
  
(* ref_base (r, b) <=> exists f, (r = b . f || r = b .[v] f) *)
let ref_base_pred ref b =
  UDPred ("ref_field", [logic_var ref; logic_var b])
  
(* not_a_ref (r) <=> forall b f, (r <> b . f && r <> b . [v] f) *)
let not_a_ref_pred ref =
  UDPred ("not_a_ref", [logic_var ref])
  
(* undef_ref (r) <=> ref_base (r, #undefined) *)
let undef_ref_pred ref =
  UDPred ("undef_ref", [logic_var ref])
  
(* ref_prim_base (r) <=> exists b, ref_base (r, b) * b #in (#B #union #M #union #N) *)
let ref_prim_base_pred ref =
  UDPred ("ref_prim_base", [logic_var ref])
  
(* type_of_pred (v, t) <=> type_of v = t *)
let type_of_pred v (t : es_lang_type) =
  UDPred ("type_of", [logic_var v; logic_string (PrintLogic.string_of_es_lang_type t)])
  
  
(* not_type_of_pred (v, t) <=> type_of v <> t *)
let not_type_of_pred v (t : es_lang_type) =
  UDPred ("not_type_of", [logic_var v; logic_string (PrintLogic.string_of_es_lang_type t)])
  
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
  
type translation_ctx = {
    env_vars : ctx_variables list; 
    return_var : variable;
    throw_var : variable;
    label_return : label;
    label_throw : label;
  }
  
let create_ctx env =
  {
     env_vars = env;
     return_var = fresh_r ();
     throw_var = fresh_r ();
     label_return = "return." ^ fresh_r ();
     label_throw = "throw." ^ fresh_r ();
  }
  
let add_proto obj proto =
  let r1 = mk_assign_fresh_lit (String (string_of_builtin_field Proto)) in
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
  let cond1 = not_a_ref_pred v1 in
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
  
let translate_call_construct_start f e1 e2s ctx =
    let r1 = f e1 in
    let r2 = mk_assign_fresh (BuiltInFunction(Gamma r1.etf_lvar)) in  
    let arg_stmts = List.map (fun e ->
        begin
          let re1 = f e in
          let re2 = mk_assign_fresh (BuiltInFunction(Gamma re1.etf_lvar)) in
          (re2.assign_left, re1.etf_stmts @ [Assignment re2])
        end
     ) e2s in  
    let arg_values, arg_stmts = List.split arg_stmts in
    let arg_stmts = List.flatten arg_stmts in  
    let cond1 = not_type_of_pred r2.assign_left Logic.LT_Object in
    let gotothrow = translate_error_throw LTError ctx.throw_var ctx.label_throw in
    let if1 = Sugar (If (cond1, gotothrow, [])) in
    let fid_ref = mk_assign_fresh (Ref(mk_ref r2.assign_left field_fid MemberReference)) in
    let hasfield = mk_assign_fresh (HasField fid_ref.assign_left) in
    let cond2 = Logic.Eq (logic_var hasfield.assign_left, logic_bool false) in
    let if2 = Sugar (If (cond2, gotothrow, [])) in
    (r1.etf_stmts @ [Assignment r2] @ arg_stmts @ [if1; Assignment fid_ref; Assignment hasfield; if2], r1, r2, arg_values)
  
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
          let r2 = mk_assign_fresh (BuiltInFunction(Gamma r1.etf_lvar)) in
          let r3 = mk_assign_fresh_lit (Pulp_Syntax.String v) in
          let r4 = mk_assign_fresh (BuiltInFunction(ObjCoercible r2.assign_left)) in
          let r5 = mk_assign_fresh (Ref(mk_ref r2.assign_left r3.assign_left MemberReference)) in
          mk_etf_return (List.flatten [r1.etf_stmts; [Assignment r2; Assignment r3; Assignment r4; Assignment r5]]) r5.assign_left;
        end
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
                  let r3 = mk_assign_fresh (BuiltInFunction(Gamma r2.etf_lvar)) in
                  let r4 = mk_assign_fresh_lit (String (Pretty_print.string_of_propname prop_name)) in
                  let r5 = mk_assign_fresh (Ref(mk_ref r1.assign_left r4.assign_left MemberReference)) in
                  let r6 = Mutation (mk_mutation r5.assign_left r3.assign_left) in
                  r2.etf_stmts @ [Assignment r3; Assignment r4; Assignment r5; r6]
                end
              | _ -> raise (PulpNotImplemented ("Getters and Setters are not yet implemented"))
            ) xs in
          let r6 = mk_assign_fresh (Var r1.assign_left) in
          mk_etf_return ([Assignment r1] @ proto_stmts @ (List.flatten stmts)) r6.assign_left 
        end
      | Parser_syntax.Assign (e1, e2) ->
        begin
          let r1 = f e1 in
          let r2 = f e2 in
          let r3 = mk_assign_fresh (BuiltInFunction(Gamma r2.etf_lvar)) in
          (* TODO: Change logic to have || *)
          let cond1 = ref_type_pred r1.etf_lvar VariableReference in
          let cond2 = ref_field_pred r1.etf_lvar "arguments" in
          let cond3 = ref_field_pred r1.etf_lvar "eval" in
          let cond12 = Logic.Star [cond1; cond2] in
          let cond13 = Logic.Star [cond1; cond3] in
          let gotothrow = translate_error_throw LRError ctx.throw_var ctx.label_throw in
          let if1 = Sugar (If (cond12, gotothrow, [])) in
          let if2 = Sugar (If (cond13, gotothrow, [])) in
          let putvalue = translate_put_value r1.etf_lvar r3.assign_left ctx.throw_var ctx.label_throw in
          let r4 = mk_assign_fresh (Var r3.assign_left) in
          mk_etf_return (List.flatten [r1.etf_stmts; r2.etf_stmts; [Assignment r3; if1; if2]; putvalue.etf_stmts; [Assignment r4]]) r4.assign_left
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
        let scope = mk_assign_fresh Obj in
        let scope_proto_stmts = add_proto scope.assign_left (Literal Null) in
        let env_stmts = Utils.flat_map (fun env -> 
          let env_scope = function_scope_name env.func_id in
          let ref_assign = mk_assign_fresh (Ref (mk_ref scope.assign_left env.func_id MemberReference)) in 
          [Assignment ref_assign; Mutation (mk_mutation ref_assign.assign_left env_scope)]
          ) ctx.env_vars in
        let f_codename_ref = mk_assign_fresh (Ref (mk_ref f_obj.assign_left field_fid MemberReference)) in
        let f_codename_update = Mutation (mk_mutation f_codename_ref.assign_left fid) in
        let f_scope_ref = mk_assign_fresh (Ref (mk_ref f_obj.assign_left field_scope MemberReference)) in
        let f_scope_update = Mutation (mk_mutation f_scope_ref.assign_left scope.assign_left) in
        let f_assign = mk_assign_fresh (Var f_obj.assign_left) in
        mk_etf_return ([Assignment f_obj] @ f_obj_proto_stmts @ [Assignment scope] @ scope_proto_stmts
                       @ env_stmts @ [Assignment f_codename_ref; f_codename_update; 
                       Assignment f_scope_ref; f_scope_update; Assignment f_assign]) f_assign.assign_left  
      | Parser_syntax.Call (e1, e2s) ->
        let stmts, r1, r2, arg_values = translate_call_construct_start f e1 e2s ctx in
			  let vthis = fresh_variable "r" in
			  let cond3 = not_a_ref_pred r1.etf_lvar in
			  let assign_vthis_und = Assignment (mk_assign vthis (Literal Undefined)) in
			  let if2 = Sugar (If (cond3, [assign_vthis_und], [])) in
			  let cond4 = ref_type_pred r1.etf_lvar VariableReference in
			  let if3 = Sugar (If (cond4, [assign_vthis_und], [])) in
			  let cond5 = ref_type_pred r1.etf_lvar MemberReference in
			  let base_assign = mk_assign_fresh (Base r1.etf_lvar) in
			  let assign_vthis_base = Assignment (mk_assign vthis (Var base_assign.assign_left)) in
			  let if4 = Sugar (If (cond5, [Assignment base_assign; assign_vthis_base], [])) in
			  (*TODO Eval*)
			  let cond6 = Logic.NEq (logic_var r2.assign_left, lb_le (Lb_Loc LEval)) in
        let fid_ref = mk_assign_fresh (Ref (mk_ref r2.assign_left field_fid MemberReference)) in
        let fid = mk_assign_fresh (Lookup fid_ref.assign_left) in
        let scope_ref = mk_assign_fresh (Ref (mk_ref r2.assign_left field_scope MemberReference)) in
        let fscope = mk_assign_fresh (Lookup scope_ref.assign_left) in
			  let call = mk_assign_fresh (Call (mk_call fid.assign_left fscope.assign_left vthis arg_values)) in
			  let if5 = Sugar (If (cond6, [Assignment fid_ref; Assignment fid; Assignment scope_ref; Assignment fscope; Assignment call], [])) in
			  mk_etf_return (stmts @ [if2; if3; if4; if5]) call.assign_left
        
      | Parser_syntax.New (e1, e2s) ->
        
        raise (Invalid_argument "WIP")
        
      | Parser_syntax.CAccess _ (* (e1, e2) *)
      | Parser_syntax.Return _ (*e*)
      | Parser_syntax.BinOp _ (*(e1, op, e2)*) 
      | Parser_syntax.If _ (*(e1, e2, e3)*)
      | Parser_syntax.While _ (*(e1, e2)*)
      | Parser_syntax.Delete _ (*e*)

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
  let current_scope = Assignment (mk_assign current_scope_var Obj) in
  let proto_stmts = add_proto current_scope_var (Literal Null) in
  let init_vars = Utils.flat_map (fun v ->
      let v_assign = mk_assign_fresh_lit (String v) in
      let ref_assign = mk_assign_fresh (Ref (mk_ref current_scope_var v_assign.assign_left VariableReference)) in 
      [Assignment v_assign; Assignment ref_assign; Mutation (mk_mutation ref_assign.assign_left v)]
    ) args in
  (* Assign undefined to var declarations *)
  (* TODO : Fix the case when we already have formal parameter with the same name *)
  let decl_vars = Utils.flat_map (fun v ->
      let v_assign = mk_assign_fresh_lit (String v) in
      let ref_assign = mk_assign_fresh (Ref (mk_ref current_scope_var v_assign.assign_left VariableReference)) in 
      let und_assign = mk_assign_fresh_lit Undefined in
      [Assignment v_assign; Assignment ref_assign; Assignment und_assign; Mutation (mk_mutation ref_assign.assign_left und_assign.assign_left)]
    ) (var_decls fb) in
  let pulpe = init_e @ [current_scope] @ proto_stmts @ init_vars @ decl_vars @ (exp_to_fb ctx fb).etf_stmts in
  make_fun_with_ctx env (make_function_block fid pulpe (rthis :: (rscope :: args)) ctx.return_var ctx.throw_var)

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
