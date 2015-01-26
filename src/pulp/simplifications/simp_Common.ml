open Pulp_Syntax

let entry = "Entry"

type edge_type =
  | Edge_Normal
  | Edge_Excep
  | Edge_True
  | Edge_False

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
    | IsTypeOf (e, _) -> f e

let is_const_stmt stmt =
  match stmt with
    | Basic (Assignment assign) ->
      begin match assign.assign_right with
        | Expression e -> is_const_expr e
        | _ -> false
      end
    | _ -> false

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
    | IsTypeOf (e, t) -> IsTypeOf (f e, t)

let update_call c var const =
  let f = update_expr var const in
  mk_call (f c.call_name) (f c.call_scope) (f c.call_this) (List.map f c.call_args)

let update_assign_expr var const e =
  let f = update_expr var const in
  match e with
	  | Expression expr -> Expression (f expr)
	  | Call c -> Call (update_call c var const)
	  | Obj -> Obj
	  | HasField (e1, e2) -> HasField (f e1, f e2)
	  | Lookup (e1, e2) -> Lookup (f e1, f e2)
	  | Deallocation (e1, e2) -> Deallocation (f e1, f e2)
	  | Pi (e1, e2) -> Pi (f e1, f e2)

let update_basic_stmt var const stmt =
  let f = update_expr var const in
  match stmt with
    | Skip -> Skip
    | Assignment {assign_left = al; assign_right = ar} -> Assignment {assign_left = al; assign_right = update_assign_expr var const ar}
    | Mutation m -> Mutation (mk_mutation (f m.m_loc) (f m.m_field) (f m.m_right))

let rec update_stmt var const stmt = 
  match stmt with
    | Label _ 
    | Goto _ -> stmt
    | GuardedGoto (e, l1, l2) -> GuardedGoto (update_expr var const e, l1, l2)
    | Basic bs -> Basic (update_basic_stmt var const bs)
    | Sugar sstmt -> Sugar (update_sugar_stmt var const sstmt)
and
update_sugar_stmt var const stmt =
  match stmt with
  | If (e, t1, t2) -> If (update_expr var const e, List.map (update_stmt var const) t1, List.map (update_stmt var const) t2)

let rec simplify_expr e = 
  let f = simplify_expr in
  match e with
    | Literal l -> e
    | Var v -> e
    | BinOp (e1, binop, e2) -> BinOp (f e1, binop, f e2) (* TODO *)
    | UnaryOp (uop, e) -> UnaryOp (uop, f e) (* TODO *)
    | Ref (e1, e2, reftype) -> 
      let fe1 = f e1 in
      let fe2 = f e2 in
      begin match fe1, fe2 with
        | Base ref1, Field ref2 -> 
          if ref1 = ref2 then ref1 else Ref (fe1, fe2, reftype)
        | _, _ -> Ref (fe1, fe2, reftype)
      end
    | Base exp -> 
      let fexp = f exp in
      begin match fexp with
        | Ref (e1, e2, reftype) -> e1
        | _ -> Base fexp
      end
    | Field exp -> 
      let fexp = f exp in
      begin match fexp with
        | Ref (e1, e2, reftype) -> e2
        | _ -> Field fexp
      end
    | IsTypeOf (exp, t) -> 
      let fexp = f exp in
      begin match t with
        | ReferenceType (Some MemberReference) ->
          begin match fexp with
            | Ref (_, _, MemberReference) ->  Literal (Bool true)
            | Ref _
            | Literal _ -> Literal (Bool false)
            | Var _ 
            | BinOp _
            | UnaryOp _
            | Base _
            | Field _
            | IsTypeOf _ -> IsTypeOf (fexp, t)
          end
        | ReferenceType (Some VariableReference) ->
          begin match fexp with
            | Ref (_, _, VariableReference) -> Literal (Bool true)
            | Ref _
            | Literal _ -> Literal (Bool false)
            | Var _ 
            | BinOp _
            | UnaryOp _
            | Base _
            | Field _
            | IsTypeOf _ -> IsTypeOf (fexp, t)
          end
        | ReferenceType None -> 
          begin match fexp with
            | Ref _ -> Literal (Bool true)
            | Literal _ -> Literal (Bool false)
            | Var _ 
            | BinOp _
            | UnaryOp _
            | Base _
            | Field _
            | IsTypeOf _ -> IsTypeOf (fexp, t)
          end
        | NullType ->
          begin match fexp with
            | Literal Null -> Literal (Bool true)
            | Literal _
            | Ref _ -> Literal (Bool false)
            | Var _ 
            | BinOp _
            | UnaryOp _
            | Base _
            | Field _
            | IsTypeOf _ -> IsTypeOf (fexp, t)
          end
        | UndefinedType ->
          begin match fexp with
            | Literal Undefined -> Literal (Bool true)
            | Literal _
            | Ref _ -> Literal (Bool false)
            | Var _ 
            | BinOp _
            | UnaryOp _
            | Base _
            | Field _
            | IsTypeOf _ -> IsTypeOf (fexp, t)
          end
        | BooleanType ->
          begin match fexp with
            | Literal (Bool _) 
            | IsTypeOf _ -> Literal (Bool true)
            | Literal _
            | Ref _ -> Literal (Bool false)
            | Var _ 
            | BinOp _
            | UnaryOp _
            | Base _
            | Field _ -> IsTypeOf (fexp, t)
          end
        | StringType ->   
          begin match fexp with
            | Literal (String _) -> Literal (Bool true)
            | Literal _
            | Ref _ -> Literal (Bool false)
            | Var _ 
            | BinOp _
            | UnaryOp _
            | Base _
            | Field _
            | IsTypeOf _ -> IsTypeOf (fexp, t)
          end
        | NumberType ->
          begin match fexp with
            | Literal (Num _) -> Literal (Bool true)
            | Literal _
            | Ref _ -> Literal (Bool false)
            | Var _ 
            | BinOp _
            | UnaryOp _
            | Base _
            | Field _
            | IsTypeOf _ -> IsTypeOf (fexp, t)
          end
        | ObjectType ->
          begin match fexp with
            | Literal (LLoc _) -> Literal (Bool true)
            | Literal _
            | Ref _ -> Literal (Bool false)
            | Var _ 
            | BinOp _
            | UnaryOp _
            | Base _
            | Field _
            | IsTypeOf _ -> IsTypeOf (fexp, t)
          end
     end
    
 let simplify_call c =
  let f = simplify_expr in
  mk_call (f c.call_name) (f c.call_scope) (f c.call_this) (List.map f c.call_args)

let simplify_assign_expr e =
  let f = simplify_expr in
  match e with
      | Expression expr -> Expression (f expr)
      | Call c -> Call (simplify_call c)
      | Obj -> Obj
      | HasField (e1, e2) -> HasField (f e1, f e2)
      | Lookup (e1, e2) -> Lookup (f e1, f e2)
      | Deallocation (e1, e2) -> Deallocation (f e1, f e2)
      | Pi (e1, e2) -> Pi (f e1, f e2)

let simplify_basic_stmt stmt =
  let f = simplify_expr in
  match stmt with
    | Skip -> Skip
    | Assignment {assign_left = al; assign_right = ar} -> Assignment {assign_left = al; assign_right = simplify_assign_expr ar}
    | Mutation m -> Mutation (mk_mutation (f m.m_loc) (f m.m_field) (f m.m_right))

let rec simplify_stmt stmt = 
  match stmt with
    | Label _ 
    | Goto _ -> stmt
    | GuardedGoto (e, l1, l2) -> GuardedGoto (simplify_expr e, l1, l2)
    | Basic bs -> Basic (simplify_basic_stmt bs)
    | Sugar sstmt -> Sugar (simplify_sugar_stmt sstmt)
and
simplify_sugar_stmt stmt =
  match stmt with
  | If (e, t1, t2) -> If (simplify_expr e, List.map simplify_stmt t1, List.map simplify_stmt t2)