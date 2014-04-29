open Pulp_Syntax
open Pulp_Syntax_Utils
open Logic

exception PulpNotImplemented of string

let fresh_variable : variable =
  let counter = ref 0 in
  let rec f =
    let v = "r" ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f
  
let rthis : variable = "rthis"
let rempty : variable = "rempty" (* Using this variable temporarily since logic at the moment does not have value "empty"*)

let end_label : label = "theend"

(* Assignment to a fresh variable *)
let mk_assign exp = { 
    assignment_left = fresh_variable; 
    assignment_right = exp
  }
  
let mk_assign_lit lit = mk_assign (Literal lit)

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
  
type labels_to_jump_to = {
    label_normal : label;
    label_return : label;
    label_throw : label;
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

let rec exp_to_fb labels exp : expr_to_fb_return = (* TODO : update labels *)
  let mk_result = mk_etf_return in
  let f = exp_to_fb labels in 
  match exp.Parser_syntax.exp_stx with
      (* Literals *)
      | Parser_syntax.Num n -> 
        begin
          let assign = mk_assign_lit (Num n) in 
          mk_result [Assignment assign] assign.assignment_left
        end
      | Parser_syntax.String s -> 
        begin 
          let assign = mk_assign_lit (String s) in 
          mk_result [Assignment assign] assign.assignment_left
        end
      | Parser_syntax.Null ->
        begin 
          let assign = mk_assign_lit Null in 
          mk_result [Assignment assign] assign.assignment_left
        end
      | Parser_syntax.Bool b -> 
        begin 
          let assign = mk_assign_lit (Bool b) in 
          mk_result [Assignment assign] assign.assignment_left
        end
      | Parser_syntax.This -> 
        begin 
          let assign = mk_assign (Var rthis) in 
          mk_result [Assignment assign] assign.assignment_left
        end
      | Parser_syntax.Var v -> 
        begin 
          let assign = mk_assign (BuiltInFunction(Sigma v)) in 
          mk_result [Assignment assign] assign.assignment_left
        end
      | Parser_syntax.Access (e, v) -> 
        begin
          let r1 = f e in
          let r2 = mk_assign (BuiltInFunction(Gamma r1.etf_lvar)) in
          let r3 = mk_assign_lit (Pulp_Syntax.String v) in
          let r4 = mk_assign (BuiltInFunction(ObjCoercible r2.assignment_left)) in
          let cond = Eq(Le_Var (AVar r4.assignment_left), Le_Var (AVar rempty)) in
          let r5 = mk_assign (Member(r2.assignment_left, r3.assignment_left)) in
          let gotoend = Goto [end_label] in
          let if_stmt = Sugar (If (cond, [Assignment r5], [gotoend])) in
          mk_etf_return (List.flatten [r1.etf_stmts; [Assignment r2; Assignment r3; Assignment r4; if_stmt]]) r5.assignment_left;
        end


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
      | Parser_syntax.Script _ (*(_, es)*)

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


let exp_to_pulp e =
  exp_to_fb (get_all_functions e)
