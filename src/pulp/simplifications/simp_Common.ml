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
  
  let e = match e with
    | Literal _ 
    | Var _ -> e
    | BinOp (e1, binop, e2) -> BinOp (f e1, binop, f e2)
    | UnaryOp (uop, e) -> UnaryOp (uop, f e)
    | Ref (e1, e2, reftype) -> Ref (f e1, f e2, reftype)
    | Base e -> Base (f e)
    | Field e -> Field (f e)
    | IsTypeOf (e, t) -> IsTypeOf (f e, t) in
  
  match e with
    | Literal _ 
    | Var _ -> e
    | BinOp (e1, binop, e2) -> 
      begin match binop with
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
                | _, _ -> Literal (Bool false)
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
      end
    | UnaryOp (Not, e1) -> 
      begin match e1 with
        | Literal (Bool b) -> Literal (Bool (not b))
        | _ -> e
      end
    | Ref (Base ref1, Field ref2, reftype) -> 
       if ref1 = ref2 then ref1 else e
    | Ref _ -> e
    | Base (Ref (e1, e2, reftype)) -> e1
    | Base _ -> e
    | Field (Ref (e1, e2, reftype)) -> e2
    | Field _ -> e
    | IsTypeOf (exp, t) -> 
      begin match t with
        | ReferenceType (Some MemberReference) ->
          begin match exp with
            | Ref (_, _, MemberReference) ->  Literal (Bool true)
            | Ref _
            | Literal _ -> Literal (Bool false)
            | Var _ 
            | BinOp _
            | UnaryOp _
            | Base _
            | Field _
            | IsTypeOf _ -> IsTypeOf (exp, t)
          end
        | ReferenceType (Some VariableReference) ->
          begin match exp with
            | Ref (_, _, VariableReference) -> Literal (Bool true)
            | Ref _
            | Literal _ -> Literal (Bool false)
            | Var _ 
            | BinOp _
            | UnaryOp _
            | Base _
            | Field _
            | IsTypeOf _ -> IsTypeOf (exp, t)
          end
        | ReferenceType None -> 
          begin match exp with
            | Ref _ -> Literal (Bool true)
            | Literal _ -> Literal (Bool false)
            | Var _ 
            | BinOp _
            | UnaryOp _
            | Base _
            | Field _
            | IsTypeOf _ -> IsTypeOf (exp, t)
          end
        | NullType ->
          begin match exp with
            | Literal Null -> Literal (Bool true)
            | Literal _
            | Ref _ -> Literal (Bool false)
            | Var _ 
            | BinOp _
            | UnaryOp _
            | Base _
            | Field _
            | IsTypeOf _ -> IsTypeOf (exp, t)
          end
        | UndefinedType ->
          begin match exp with
            | Literal Undefined -> Literal (Bool true)
            | Literal _
            | Ref _ -> Literal (Bool false)
            | Var _ 
            | BinOp _
            | UnaryOp _
            | Base _
            | Field _
            | IsTypeOf _ -> IsTypeOf (exp, t)
          end
        | BooleanType ->
          begin match exp with
            | Literal (Bool _) 
            | IsTypeOf _ -> Literal (Bool true)
            | Literal _
            | Ref _ -> Literal (Bool false)
            | Var _ 
            | BinOp _
            | UnaryOp _
            | Base _
            | Field _ -> IsTypeOf (exp, t)
          end
        | StringType ->   
          begin match exp with
            | Literal (String _) -> Literal (Bool true)
            | Literal _
            | Ref _ -> Literal (Bool false)
            | Var _ 
            | BinOp _
            | UnaryOp _
            | Base _
            | Field _
            | IsTypeOf _ -> IsTypeOf (exp, t)
          end
        | NumberType ->
          begin match exp with
            | Literal (Num _) -> Literal (Bool true)
            | Literal _
            | Ref _ -> Literal (Bool false)
            | Var _ 
            | BinOp _
            | UnaryOp _
            | Base _
            | Field _
            | IsTypeOf _ -> IsTypeOf (exp, t)
          end
        | ObjectType ->
          begin match exp with
            | Literal (LLoc _) -> Literal (Bool true)
            | Literal _
            | Ref _ -> Literal (Bool false)
            | Var _ 
            | BinOp _
            | UnaryOp _
            | Base _
            | Field _
            | IsTypeOf _ -> IsTypeOf (exp, t)
          end
     end
    
 (* TODO : cleanup : make a generic functions stmt (f : expr->expr) -> stmt *)
    
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