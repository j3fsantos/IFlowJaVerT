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
    | IsTypeOf (e, t) -> raise (NotImplemented "is type of deprecated")
    | TypeOf e -> Le_TypeOf (f e)

let small_axiom_basic_stmt bs : (formula * formula) list =
  match bs with
    | Skip -> [empty_f, empty_f]
    | Assignment a ->
      let var = Le_PVar a.assign_left in
      begin match a.assign_right with
        | Expression e -> 
          let old = fresh_e () in
          let logic_e = expr_to_logical_expr e in
          [Eq (var, Le_Var old), Eq (var, subs_pvar_in_exp a.assign_left (Le_Var old) logic_e)]
        | Call _ 
        | Eval _
        | BuiltinCall _ -> raise (Invalid_argument "Call")
        | Obj ->
          let l = Le_Var (fresh_e ()) in 
          [empty_f, 
          Star [
            Eq (var, l);
            ObjFootprint (l, [])
          ]]
        | HasField (e1, e2) -> 
          (* TODO: Heaplet should have logical_exp instead of string *)
          (*let l = fresh_loc_e () in
          let e1_logical = expr_to_logical_expr e1 in
          [ Star [
              Eq (Le_Value (Lv_Loc (Lb_Loc l)), e1_logical);
              Logic.HeapletEmpty (l, expr_to_logical_expr e2)
            ], 
	          Star [
              Eq (Le_Value (Lv_Loc (Lb_Loc l)), e1_logical);
	            Logic.HeapletEmpty (expr_to_logical_expr e1, expr_to_logical_expr e2); 
	            Eq (var, Le_Value (Lv_Value (LT_Boolean false)));
	           ]
            
          ]*)
          raise (NotImplemented "HasField")
        | Lookup (e1, e2) -> raise (NotImplemented "Lookup")
        | Deallocation (e1, e2) -> raise (NotImplemented "Deallocation")
        | ProtoF (e1, e2) -> raise (NotImplemented "ProtoField")
        | ProtoO (e1, e2) -> raise (NotImplemented "ProtoObj")
      end
    | Mutation m -> raise (NotImplemented "Mutation")