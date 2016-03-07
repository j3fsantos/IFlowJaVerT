(* ./src/pulp/simplifications/simp_Common.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open Pulp_Syntax
open Type_Info

type specs_func_simp_type  =
  | Simp_Unfold_Specs
  | Simp_Specs


type edge_type =
  | Edge_Normal
  | Edge_Excep
  | Edge_True
  | Edge_False

type annotation = {
  annot_type_info : (variable * type_info) list
}

let string_of_annotation a =
  match a with 
    | None -> ""
    | Some a -> " | " ^ (String.concat ", " (List.map (fun (v, ty) -> v ^ (string_of_type_info ty)) a.annot_type_info))

type annotated_statement = {
  as_stmt : statement; 
  as_annot : annotation option
}

let string_of_annot_stmt s =
  (Pulp_Syntax_Print.string_of_statement s.as_stmt) ^ (string_of_annotation s.as_annot)
  
let string_of_annot_stmts stmts =
  String.concat "\n" (List.map string_of_annot_stmt stmts)
  
let as_annot_stmt stmt = {as_stmt = stmt; as_annot = None}

let as_annot_stmt_empty_data stx = {as_stmt = mk_stmt_empty_data stx; as_annot = None}

let as_annot_stmts stmts = List.map as_annot_stmt stmts

let remove_annot annot_stmt = annot_stmt.as_stmt

let remove_annots annot_stmts = List.map remove_annot annot_stmts

let get_type_info annot var = 
  match annot with 
    | None -> None
    | Some annot -> 
      begin try
        let _, ty = List.find (fun (v, ty) -> var = v) annot.annot_type_info in
        Some ty
      with Not_found -> None 
  end

let rec get_vars_in_expr e =
  let f = get_vars_in_expr in
  match e with
    | Literal l -> []
    | Var v -> [v]
    | BinOp (e1, _, e2) -> f e1 @ f e2
    | UnaryOp (_, e) -> f e
    | Ref (e1, e2, _) -> f e1 @ f e2
    | Base e -> f e
    | Field e -> f e
    | TypeOf e -> f e

let get_vars_in_call c  =
  let f = get_vars_in_expr in
  (f c.call_name) @ (f c.call_scope) @ (f c.call_this) @ (List.flatten (List.map f c.call_args))

let get_vars_in_assign_expr e =
  let f = get_vars_in_expr in
  match e with
      | Expression expr -> f expr
      | Call c 
      | Eval c 
      | BuiltinCall c -> get_vars_in_call c
      | Obj -> []
      | HasField (e1, e2) -> f e1 @ f e2
      | Lookup (e1, e2) -> f e1 @ f e2
      | Deallocation (e1, e2) -> f e1 @ f e2
      | ProtoF (e1, e2) -> f e1 @ f e2
      | ProtoO (e1, e2) -> f e1 @ f e2

let get_vars_in_bs_stmt stmt =
  let f = get_vars_in_expr in
  match stmt with
    | Skip -> []
    | Assignment {assign_left = al; assign_right = ar} -> get_vars_in_assign_expr ar
    | Mutation m -> (f m.m_loc) @ (f m.m_field) @ (f m.m_right)

let get_vars_in_spec_functions sf =
  let f = get_vars_in_expr in
  match sf with
    | GetValue e  
    | DefaultValue (e, _)
    | ToPrimitive (e, _) 
    | ToBoolean e 
    | ToNumber e
    | ToNumberPrim e 
    | ToString e 
    | ToStringPrim e 
    | ToObject e 
    | CheckObjectCoercible e 
    | IsCallable e -> f e
    | Get (e1, e2)
    | HasProperty (e1, e2)
    | PutValue (e1, e2)  
    | AbstractRelation (e1, e2, _) 
    | StrictEquality (e1, e2)
    | StrictEqualitySameType (e1, e2) -> (f e1) @ (f e2)

let rec get_vars_in_stmt stmt = 
  match stmt.stmt_stx with
    | Label _ 
    | Goto _ -> []
    | GuardedGoto (e, l1, l2) -> get_vars_in_expr e
    | Basic bs -> get_vars_in_bs_stmt bs
    | Sugar sstmt -> get_vars_in_sugar_stmt sstmt
and
get_vars_in_sugar_stmt stmt =
  match stmt with
  | If (e, t1, t2) -> (get_vars_in_expr e) @ (List.flatten (List.map get_vars_in_stmt t1)) @ (List.flatten (List.map get_vars_in_stmt t2))
  | SpecFunction (left, sf, excep_label) -> left :: (get_vars_in_spec_functions sf)

let rec is_const_expr e =
  let f = is_const_expr in
  match e with
    | Literal _ -> true
    | Var _ -> false
    | BinOp (e1, _, e2) -> (f e1) && (f e2)
    | UnaryOp (_, e) -> f e
    | Ref (e1, e2, _) -> (f e1) && (f e2)
    | Base e -> f e
    | Field e -> f e
    | TypeOf e -> f e

let is_const_stmt stmt =
  match stmt with
    | Basic (Assignment assign) ->
      begin match assign.assign_right with
        | Expression e -> is_const_expr e
        | _ -> false
      end
    | _ -> false

 (* A generic functions stmt (f : expr->expr) -> stmt *)

let transform_expr_in_call f c =
  mk_call (f c.call_name) (f c.call_scope) (f c.call_this) (List.map f c.call_args) (c.call_throw_label)
  
let transform_expr_in_spec_funcs f sf =
  match sf with
    | GetValue e -> GetValue (f e)
    | Get (e1, e2) -> Get (f e1, f e2)
    | HasProperty (e1, e2) -> HasProperty (f e1, f e2)
    | DefaultValue (e, pt) -> DefaultValue (f e, pt)
    | ToPrimitive (e, pt) -> ToPrimitive (f e, pt)
    | ToBoolean e -> ToBoolean (f e)
    | ToNumber e -> ToNumber (f e)
    | ToNumberPrim e -> ToNumberPrim (f e)
    | ToString e -> ToString (f e)
    | ToStringPrim e -> ToStringPrim (f e)
    | ToObject e -> ToObject (f e)
    | CheckObjectCoercible e -> CheckObjectCoercible (f e)
    | IsCallable e -> IsCallable (f e)
    | PutValue (e1, e2) -> PutValue (f e1, f e2)
    | AbstractRelation (e1, e2, b) -> AbstractRelation (f e1, f e2, b)
    | StrictEquality (e1, e2) -> StrictEquality (f e1, f e2)
    | StrictEqualitySameType (e1, e2) -> StrictEqualitySameType (f e1, f e2)

let transform_expr_in_assign_expr f e =
  match e with
      | Expression expr -> Expression (f expr)
      | Call c -> Call (transform_expr_in_call f c)
      | Eval c -> Eval (transform_expr_in_call f c)
      | BuiltinCall c -> BuiltinCall (transform_expr_in_call f c)
      | Obj -> Obj
      | HasField (e1, e2) -> HasField (f e1, f e2)
      | Lookup (e1, e2) -> Lookup (f e1, f e2)
      | Deallocation (e1, e2) -> Deallocation (f e1, f e2)
      | ProtoF (e1, e2) -> ProtoF (f e1, f e2)
      | ProtoO (e1, e2) -> ProtoO (f e1, f e2)

let transform_expr_in_basic_stmt f stmt =
  match stmt with
    | Skip -> Skip
    | Assignment {assign_left = al; assign_right = ar} -> 
      Assignment {assign_left = al; assign_right = transform_expr_in_assign_expr f ar}
    | Mutation m -> Mutation (mk_mutation (f m.m_loc) (f m.m_field) (f m.m_right))

let rec transform_expr_in_stmt f stmt = 
  match stmt.stmt_stx with
    | Label _ 
    | Goto _ -> stmt
    | GuardedGoto (e, l1, l2) -> {stmt with stmt_stx = GuardedGoto (f e, l1, l2)}
    | Basic bs -> {stmt with stmt_stx = Basic (transform_expr_in_basic_stmt f bs)}
    | Sugar sstmt -> {stmt with stmt_stx = Sugar (transform_expr_in_sugar_stmt f sstmt)}
and
transform_expr_in_sugar_stmt f stmt =
  match stmt with
  | If (e, t1, t2) -> If (f e, List.map (transform_expr_in_stmt f) t1, List.map (transform_expr_in_stmt f) t2)
  | SpecFunction (left, sf, excep_label) -> SpecFunction (left, transform_expr_in_spec_funcs f sf, excep_label)


(* Constant Propagation *)

let rec update_expr var const e =
  let f = update_expr var const in
  match e with
    | Literal l -> e
    | Var v -> if v = var then const else Var v
    | BinOp (e1, binop, e2) -> BinOp (f e1, binop, f e2)
    | UnaryOp (uop, e) -> UnaryOp (uop, f e)
    | Ref (e1, e2, reftype) -> Ref (f e1, f e2, reftype)
    | Base e -> Base (f e)
    | Field e -> Field (f e)
    | TypeOf (e) -> TypeOf (f e)

let update_stmt var const stmt = transform_expr_in_stmt (update_expr var const) stmt

let rec simplify_expr e = 
  let f = simplify_expr in
  
  let e = match e with
    | Literal _ 
    | Var _ -> e
    | BinOp (e1, binop, e2) -> BinOp (f e1, binop, f e2)
    | UnaryOp (uop, e) -> UnaryOp (uop, f e)
    | Ref (e1, e2, reftype) -> Ref (f e1, f e2, reftype)
    | Base e -> Base (f e)
    | Field e -> Field (f e)
    | TypeOf (e) -> TypeOf (f e) in
  
  match e with
    | Literal _ 
    | Var _ -> e
    | BinOp (e1, binop, e2) -> 
      begin match binop with
        | Concat ->
          begin match e1, e2 with
            | Literal (String s1), (Literal (String s2)) -> Literal (String (s1 ^ s2))
            | _ -> e
          end
        | Comparison Equal ->
          begin match e1, e2 with
            | Literal lit1, Literal lit2 ->
              begin match lit1, lit2 with
                | LLoc l1, LLoc l2 -> Literal (Bool (l1 = l2))
							  | Null, Null -> Literal (Bool true)                  
							  | Bool b1, Bool b2 -> Literal (Bool (b1 = b2))         
							  | Num n1, Num n2 -> Literal (Bool (n1 = n2))         
							  | String s1, String s2 -> Literal (Bool (s1 = s2))  
							  | Undefined, Undefined -> Literal (Bool true)   
							  | Empty, Empty -> Literal (Bool true) 
                | Type t1, Type t2 -> Literal (Bool (t1 = t2))
                | _, _ -> Literal (Bool false)
              end
            | _ -> e
          end
        | Comparison LessThan ->
          begin match e1, e2 with
            | Literal lit1, Literal lit2 ->
              begin match lit1, lit2 with                         
                | Num n1, Num n2 -> Literal (Bool (n1 < n2))        
                | _, _ -> e
              end
            | _ -> e
          end
        | Comparison LessThanEqual -> e (* TODO *)
        | Subtype ->
          begin match e1, e2 with
            | Literal lit1, Literal lit2 ->
              begin match lit1, lit2 with                         
                | Type t1, Type t2 -> Literal (Bool (is_subtype t1 t2))      
                | _, _ -> e
              end
            | _ -> e
          end
        | Arith aop -> e (* TODO *)
        | Boolean Or ->
          begin match e1, e2 with
            | Literal (Bool true), e2 -> Literal (Bool true)
            | Literal (Bool false), e2 -> e2
            | e1, Literal (Bool true) -> Literal (Bool true)
            | e1, Literal (Bool false) -> e1
            | _, _ -> e
          end
        | Boolean And ->
          begin match e1, e2 with
            | Literal (Bool true), e2 -> e2
            | Literal (Bool false), e2 -> Literal (Bool false)
            | e1, Literal (Bool true) -> e1
            | e1, Literal (Bool false) -> Literal (Bool false)
            | _, _ -> e
          end
        | Bitwise _ -> e
      end
    | UnaryOp (Not, e1) -> 
      begin match e1 with
        | Literal (Bool b) -> Literal (Bool (not b))
        | _ -> e
      end
    | UnaryOp (Negative, e1) -> 
      begin match e1 with
        | Literal (Num b) -> Literal (Num (-.b))
        | _ -> e
      end
    | UnaryOp _ -> e (* TODO *)
    | Ref (Base ref1, Field ref2, reftype) -> 
       if ref1 = ref2 then ref1 else e
    | Ref _ -> e
    | Base (Ref (e1, e2, reftype)) -> e1
    | Base _ -> e
    | Field (Ref (e1, e2, reftype)) -> e2
    | Field _ -> e
	  | TypeOf exp ->   
      match get_type_info_expr empty_type_info exp with
        | None -> e
        | Some ti -> 
          begin match get_pulp_type ti with
            | None -> e
            | Some pt -> Literal (Type pt)
          end
   
let simplify_stmt stmt = transform_expr_in_stmt simplify_expr stmt

let rec simplify_type_of type_info e =
  let f = simplify_type_of type_info in
  match e with
    | TypeOf e1 -> TypeOf (f e1)
    | Literal _
    | Var _ -> e
    | BinOp (e1, binop, e2) -> 
      begin match binop with 
        | Comparison Equal ->
          begin match (e1, e2) with
            | TypeOf(exp), Literal (Type t) ->
              begin
                let fexp = f exp in
                let fe_type = get_type_info_expr type_info fexp in
				        let t1 = Some (TI_Type t) in
				        if (fe_type = t1) then Literal (Bool true)               
				        else if upper_bound_type fe_type t1 = fe_type then BinOp (f e1, binop, e2)
				        else Literal (Bool false)
             end
            | _ -> 
              begin
	              let e1_type = get_type_info_expr type_info e1 in
	              let e2_type = get_type_info_expr type_info e2 in
	              let upper = upper_bound_type e1_type e2_type in
	              if upper <> e1_type && upper <> e2_type then Literal (Bool false)
	              else BinOp (f e1, binop, f e2)
              end
           end
        | Subtype ->
          begin match (e1, e2) with
            | TypeOf(exp), Literal (Type t) ->
              begin
                let fe_type = get_type_info_expr type_info (f exp) in
                if ground_type t then Literal (Bool false)
                else begin
                  let t1 = Some (TI_Type t) in
                  if (upper_bound_type fe_type t1 = t1) then Literal (Bool true)
                  else if (upper_bound_type fe_type t1 <> fe_type) then Literal (Bool false)
                       else BinOp (f e1, binop, Literal (Type t)) 
               end
             end
            | _ -> BinOp (f e1, binop, f e2)
           end
        | _ -> BinOp (f e1, binop, f e2)
      end
    | UnaryOp (uop, e) -> UnaryOp (uop, f e)
    | Ref (e1, e2, reftype) -> Ref (f e1, f e2, reftype)
    | Base e -> Base (f e)
    | Field e -> Field (f e)

let simplify_type_of_in_stmt type_info stmt =
  transform_expr_in_stmt (simplify_type_of type_info) stmt