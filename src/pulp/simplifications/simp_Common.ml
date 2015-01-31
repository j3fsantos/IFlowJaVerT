open Pulp_Syntax

let entry = "Entry"

type edge_type =
  | Edge_Normal
  | Edge_Excep
  | Edge_True
  | Edge_False

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
    | IsTypeOf (e, _) -> f e

let get_vars_in_call c  =
  let f = get_vars_in_expr in
  (f c.call_name) @ (f c.call_scope) @ (f c.call_this) @ (List.flatten (List.map f c.call_args))

let get_vars_in_assign_expr e =
  let f = get_vars_in_expr in
  match e with
      | Expression expr -> f expr
      | Call c -> get_vars_in_call c
      | Obj -> []
      | HasField (e1, e2) -> f e1 @ f e2
      | Lookup (e1, e2) -> f e1 @ f e2
      | Deallocation (e1, e2) -> f e1 @ f e2
      | Pi (e1, e2) -> f e1 @ f e2

let get_vars_in_bs_stmt stmt =
  let f = get_vars_in_expr in
  match stmt with
    | Skip -> []
    | Assignment {assign_left = al; assign_right = ar} -> get_vars_in_assign_expr ar
    | Mutation m -> (f m.m_loc) @ (f m.m_field) @ (f m.m_right)

let rec get_vars_in_stmt stmt = 
  match stmt with
    | Label _ 
    | Goto _ -> []
    | GuardedGoto (e, l1, l2) -> get_vars_in_expr e
    | Basic bs -> get_vars_in_bs_stmt bs
    | Sugar sstmt -> get_vars_in_sugar_stmt sstmt
and
get_vars_in_sugar_stmt stmt =
  match stmt with
  | If (e, t1, t2) -> (get_vars_in_expr e) @ (List.flatten (List.map get_vars_in_stmt t1)) @ (List.flatten (List.map get_vars_in_stmt t2))

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

 (* A generic functions stmt (f : expr->expr) -> stmt *)

let transform_expr_in_call f c =
  mk_call (f c.call_name) (f c.call_scope) (f c.call_this) (List.map f c.call_args)

let transform_expr_in_assign_expr f e =
  match e with
      | Expression expr -> Expression (f expr)
      | Call c -> Call (transform_expr_in_call f c)
      | Obj -> Obj
      | HasField (e1, e2) -> HasField (f e1, f e2)
      | Lookup (e1, e2) -> Lookup (f e1, f e2)
      | Deallocation (e1, e2) -> Deallocation (f e1, f e2)
      | Pi (e1, e2) -> Pi (f e1, f e2)

let transform_expr_in_basic_stmt f stmt =
  match stmt with
    | Skip -> Skip
    | Assignment {assign_left = al; assign_right = ar} -> 
      Assignment {assign_left = al; assign_right = transform_expr_in_assign_expr f ar}
    | Mutation m -> Mutation (mk_mutation (f m.m_loc) (f m.m_field) (f m.m_right))

let rec transform_expr_in_stmt f stmt = 
  match stmt with
    | Label _ 
    | Goto _ -> stmt
    | GuardedGoto (e, l1, l2) -> GuardedGoto (f e, l1, l2)
    | Basic bs -> Basic (transform_expr_in_basic_stmt f bs)
    | Sugar sstmt -> Sugar (transform_expr_in_sugar_stmt f sstmt)
and
transform_expr_in_sugar_stmt f stmt =
  match stmt with
  | If (e, t1, t2) -> If (f e, List.map (transform_expr_in_stmt f) t1, List.map (transform_expr_in_stmt f) t2)


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
    
let simplify_stmt stmt = transform_expr_in_stmt simplify_expr stmt

type type_info = 
  | TI_Type of pulp_type
  | TI_Value (*Not a Reference && Not Empty*)
  | TI_Empty

let upper_bound_type t1 t2 =
  if t1 = t2 then t1 else 
    begin match t1, t2 with
      | None, _ -> None
      | _, None -> None
      | Some t1, Some t2 -> 
        begin match t1, t2 with
          | TI_Type (ReferenceType _), TI_Type (ReferenceType _) -> Some (TI_Type (ReferenceType None))
          | TI_Type (ReferenceType _), _ -> None
          | _, TI_Type (ReferenceType _) -> None
          | TI_Empty, _ -> None
          | _, TI_Empty -> None
          | _, _ -> Some (TI_Value)
        end
    end

let get_type_info_literal lit =
  Some (match lit with
    | LLoc _ -> TI_Type ObjectType
    | Null -> TI_Type NullType               
    | Bool _ -> TI_Type BooleanType         
    | Num _ -> TI_Type NumberType          
    | String _ -> TI_Type StringType
    | Undefined -> TI_Type UndefinedType
    | Empty -> TI_Empty)

let rec get_type_info_expr type_info e =
  let f = get_type_info_expr type_info in
  match e with
    | Literal l -> get_type_info_literal l
    | Var v -> type_info v
    | BinOp (e1, binop, e2) -> 
      let e1_type = f e1 in
      let e2_type = f e2 in
      begin match binop with
        | Comparison Equal -> if e1_type = e2_type then Some (TI_Type BooleanType) else None
        | Arith aop ->
          begin match aop with
            | Plus ->
              begin
                if e1_type = e2_type then
                  if e1_type = Some (TI_Type StringType) || e1_type = Some (TI_Type NumberType) then e1_type
                  else None
                else None
              end
            | Minus 
            | Times
            | Div -> if e1_type = e2_type && e1_type = Some (TI_Type NumberType) then Some (TI_Type NumberType)
                     else None
         end
        | Boolean bop -> if e1_type = e2_type && e1_type = Some (TI_Type BooleanType) then Some (TI_Type BooleanType)
                         else None
      end
    | UnaryOp (Not, e) -> 
      let e_type = f e in
      if e_type = Some (TI_Type BooleanType) then Some (TI_Type BooleanType)
      else None
    | Ref (e1, e2, ref_type) -> Some (TI_Type (ReferenceType (Some ref_type)))
    | Base e -> Some TI_Value
    | Field e -> Some (TI_Type StringType)
    | IsTypeOf (e, _) -> Some (TI_Type BooleanType)

let get_type_info_assign_expr type_info e =
  let f = get_type_info_expr type_info in
  match e with
      | Expression expr -> f expr
      | Call c -> Some TI_Value
      | Obj -> Some (TI_Type ObjectType)
      | HasField (e1, e2) -> Some (TI_Type BooleanType)
      | Lookup (e1, e2) -> Some TI_Value
      | Deallocation (e1, e2) -> Some (TI_Type BooleanType)
      | Pi (e1, e2) -> Some TI_Value

let rec simplify_type_of type_info e =
  let f = simplify_type_of type_info in
  match e with
    | IsTypeOf (e1, t) -> 
      let fe_type = get_type_info_expr type_info e1 in
      let t = Some (TI_Type t) in
      if upper_bound_type fe_type t = t then
        Literal (Bool true)
      else if upper_bound_type fe_type t = fe_type then e
      else Literal (Bool false)
    | Literal _
    | Var _ -> e
    | BinOp (e1, binop, e2) -> BinOp (f e1, binop, f e2)
    | UnaryOp (uop, e) -> UnaryOp (uop, f e)
    | Ref (e1, e2, reftype) -> Ref (f e1, f e2, reftype)
    | Base e -> Base (f e)
    | Field e -> Field (f e)

let simplify_type_of_in_stmt type_info stmt =
  transform_expr_in_stmt (simplify_type_of type_info) stmt