open Pulp_Syntax
open Pulp_Syntax_Utils
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
  
let fresh_name =
  let counter = ref 0 in
  let rec f name =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f
  
let fresh_annonymous () : string =
  fresh_name "annonymous"
  
let fresh_named n : string =
  fresh_name (n ^ "_annonymous")
  
let rthis : variable = "rthis"
let rempty : variable = "rempty" (* Using this variable temporarily since logic at the moment does not have value "empty"*)

let end_label : label = "theend"

(* Assignment *)
let mk_assign var exp = { 
    assignment_left = var; 
    assignment_right = exp
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
    return_var : variable;
    throw_var : variable;
    label_return : label;
    label_throw : label;
  }
  
let create_ctx () =
  {
     return_var = fresh_r ();
     throw_var = fresh_r ();
     label_return = "return." ^ fresh_r ();
     label_throw = "throw." ^ fresh_r ();
  }
  
let join_etf_results (results : expr_to_fb_return list) : expr_to_fb_return =
  if List.length results = 0 then raise (Invalid_argument "A list argument for the join_etf_results function should not be empty")
  else
  begin
    let lvar = (List.nth results (List.length results - 1)).etf_lvar in
    List.fold_left (fun joined left_to_join -> 
      mk_etf_return (joined.etf_stmts @ left_to_join.etf_stmts) lvar
    ) (mk_etf_return [] lvar) results
  end

let rec exp_to_fb ctx exp : expr_to_fb_return = 
  let mk_result = mk_etf_return in
  let f = exp_to_fb ctx in 
  match exp.Parser_syntax.exp_stx with
      (* Literals *)
      | Parser_syntax.Num n -> 
        begin
          let assign = mk_assign_fresh_lit (Num n) in 
          mk_result [Assignment assign] assign.assignment_left
        end
      | Parser_syntax.String s -> 
        begin 
          let assign = mk_assign_fresh_lit (String s) in 
          mk_result [Assignment assign] assign.assignment_left
        end
      | Parser_syntax.Null ->
        begin 
          let assign = mk_assign_fresh_lit Null in 
          mk_result [Assignment assign] assign.assignment_left
        end
      | Parser_syntax.Bool b -> 
        begin 
          let assign = mk_assign_fresh_lit (Bool b) in 
          mk_result [Assignment assign] assign.assignment_left
        end
      | Parser_syntax.This -> 
        begin 
          let assign = mk_assign_fresh (Var rthis) in 
          mk_result [Assignment assign] assign.assignment_left
        end
      | Parser_syntax.Var v -> 
        begin 
          let var = mk_assign_fresh_lit (String v) in
          let sigma = mk_assign_fresh (BuiltInFunction(Sigma var.assignment_left)) in 
          mk_result [Assignment var; Assignment sigma] sigma.assignment_left
        end
      | Parser_syntax.Access (e, v) -> 
        begin
          let r1 = f e in
          let r2 = mk_assign_fresh (BuiltInFunction(Gamma r1.etf_lvar)) in
          let r3 = mk_assign_fresh_lit (Pulp_Syntax.String v) in
          let r4 = mk_assign_fresh (BuiltInFunction(ObjCoercible r2.assignment_left)) in
          let r5 = mk_assign_fresh (Member(r2.assignment_left, r3.assignment_left)) in
          mk_etf_return (List.flatten [r1.etf_stmts; [Assignment r2; Assignment r3; Assignment r4; Assignment r5]]) r5.assignment_left;
        end
      | Parser_syntax.Script (_, es) ->
        join_etf_results (List.map f es)
      | Parser_syntax.Delete _ (*e*)
      | Parser_syntax.BinOp _ (*(e1, op, e2)*)
      | Parser_syntax.Assign _ (*(e1, e2)*)  
      | Parser_syntax.CAccess _ (* (e1, e2) *)
      | Parser_syntax.Call _ (*(e1, e2s)*)
      | Parser_syntax.New _ (*(e1, e2s)*)
      | Parser_syntax.AnnonymousFun _ (*(_, vs, e)*) 
      | Parser_syntax.NamedFun _ (*(_, n, vs, e)*)
      | Parser_syntax.Obj _ (*xs*)
      | Parser_syntax.Skip
      | Parser_syntax.Return _ (*e*)
      | Parser_syntax.VarDec _ (*vars*)
      | Parser_syntax.While _ (*(e1, e2)*)
      | Parser_syntax.If _ (*(e1, e2, e3)*)
      | Parser_syntax.Block _ (*es*)

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
        
let translate_function fb codename args =
  let ctx = create_ctx () in
  let pulpe = (exp_to_fb ctx fb).etf_stmts in
  make_function_block codename pulpe args ctx.return_var ctx.throw_var

(* TODO: use codename from annotations if provided *)
let make_function_blocks es =
  List.map (fun e ->
    match e.Parser_syntax.exp_stx with
      | Parser_syntax.AnnonymousFun (_, args, fb) -> translate_function fb (fresh_annonymous ()) args
      | Parser_syntax.NamedFun (_, name, args, fb) -> translate_function fb (fresh_named name) args
      | _ -> raise (Invalid_argument "Should be a function definition here")
    ) es

let exp_to_pulp e =
  let main = translate_function e "main" [] in
  let all_functions = make_function_blocks (get_all_functions e) in
  main:: all_functions
