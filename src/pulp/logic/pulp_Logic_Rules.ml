open Pulp_Logic
open Pulp_Logic_Utils
open Pulp_Syntax
exception NotImplemented of string

let builtin_loc_to_logical_loc bl =
  raise (NotImplemented "builtin_loc_to_logical_loc")

let rec expr_to_logical_expr expr : logical_exp =
  let f = expr_to_logical_expr in
  match expr with
    | Literal l -> Le_Literal l
    | Var v -> Le_PVar v
    | BinOp (e1, op, e2) -> Le_BinOp (f e1, op, f e2)
    | UnaryOp (op, e) -> Le_UnOp (op, f e)
    | Ref (e1, e2, rt) -> Le_Ref (f e1, f e2, rt)
    | Base e -> Le_Base (f e)
    | Field e -> Le_Field (f e)
    | TypeOf e -> Le_TypeOf (f e)

let small_axiom_basic_stmt bs : (formula * formula) =
  let f = expr_to_logical_expr in
  match bs with
    | Skip -> empty_f, empty_f
    | Assignment a ->
      let var = Le_PVar a.assign_left in
      begin match a.assign_right with
        | Expression e -> 
          (* Only valid if in DSA form. At the moment it is not used. *)
          let old = fresh_e () in
          let logic_e = expr_to_logical_expr e in
          Eq (var, Le_Var old), Eq (var, subs_pvar_in_exp a.assign_left (Le_Var old) logic_e)
        | Call _ 
        | Eval _
        | BuiltinCall _ -> raise (Invalid_argument "Call")
        | Obj ->
          let l = Le_Var (fresh_e ()) in 
          empty_f, 
          Star [
            Eq (var, l);
            ObjFootprint (l, []);
            Eq (Le_TypeOf l, Le_Literal (Type (ObjectType (Some Normal))))
          ]
        | HasField (e1, e2) -> 
          let v = Le_Var (fresh_e ()) in 
          Heaplet (f e1, f e2, v), 
	          Star [
	            Heaplet (f e1, f e2, v); 
	            Eq (var, (Le_UnOp (Not, (Le_BinOp (v, Comparison Equal, Le_None)))));
	           ];
                        
          
        | Lookup (e1, e2) -> 
          let v = Le_Var (fresh_e ()) in 
          Star [ 
            Heaplet (f e1, f e2, v);
            NEq (v, Le_None)
          ],
          Star [ 
            Heaplet (f e1, f e2, v);
            NEq (v, Le_None);
            Eq (var, v)
          ]
          
        | Deallocation (e1, e2) -> 
          let v = Le_Var (fresh_e ()) in          
          Heaplet (f e1, f e2, v),
          Star [ 
            Heaplet (f e1, f e2, Le_None);
            Eq (var, Le_Literal (Bool true))
          ]
          
        | ProtoF (e1, e2) -> raise (Invalid_argument "ProtoF")
        | ProtoO (e1, e2) -> raise (Invalid_argument "ProtoO")
      end
    | Mutation m -> 
      let v = Le_Var (fresh_e ()) in
      Heaplet (f m.m_loc, f m.m_field, v),
      Heaplet (f m.m_loc, f m.m_field, f m.m_right)
     