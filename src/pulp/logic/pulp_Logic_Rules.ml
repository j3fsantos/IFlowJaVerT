open Logic
open Logic_Utils
open Pulp_Syntax
exception NotImplemented of string

let builtin_loc_to_logical_loc bl =
  raise (NotImplemented "builtin_loc_to_logical_loc")

let lit_to_logical_expr lit : Logic.logical_exp =
  match lit with
    | LLoc bl -> Le_Value (Lv_Loc (builtin_loc_to_logical_loc bl))
	  | Null -> Le_Value (Lv_Value Pv_Null)                  
	  | Bool b -> Le_Value (Lv_Value (Pv_Bool b))         
	  | Num n -> Le_Value (Lv_Value (Pv_Num n))       
	  | String s -> Le_Value (Lv_Value (Pv_String s))  
	  | Undefined -> Le_Value (Lv_Value Pv_Undefined)
	  | Type pt -> raise (NotImplemented "lit_to_logical_expr Type")
	  | Empty -> Le_Value (Lv_Value Pv_Empty)

let bin_op_to_logical_op op =
  raise (NotImplemented "bin_op_to_logical_op")
  
let unary_op_to_logical_op op =
  raise (NotImplemented "unary_op_to_logical_op")

let rec expr_to_logical_expr expr : Logic.logical_exp =
  let f = expr_to_logical_expr in
  match expr with
    | Literal l -> lit_to_logical_expr l
    | Var v -> Le_Var (PVar v)
    | BinOp (e1, op, e2) -> Le_BinOp (f e1, bin_op_to_logical_op op, f e2)
    | UnaryOp (op, e) -> Le_UnOp (unary_op_to_logical_op op, f e)
    | Ref (e1, e2, rt) -> raise (NotImplemented "lit_to_logical_expr Type")
    | Base e -> Le_Base (f e)
    | Field e -> Le_Field (f e)
    | IsTypeOf (e, t) -> raise (NotImplemented "is type of deprecated")
    | TypeOf e -> Le_TypeOf (f e)

let small_axiom_basic_stmt bs : formula * formula =
  match bs with
    | Skip -> empty_f, empty_f
    | Assignment a ->
      let var = Le_Var (PVar a.assign_left) in
      begin match a.assign_right with
        | Expression e -> 
          let old = fresh_e () in
          let logic_e = expr_to_logical_expr e in
          let vmap = VarMap.add (PVar a.assign_left) old VarMap.empty in
          Logic.Eq (var, Le_Var old), Logic.Eq (var, subs_vars_in_exp vmap logic_e)
        | Call _ 
        | Eval _
        | BuiltinCall _ -> raise (Invalid_argument "Call")
        | Obj ->
          let l = fresh_loc_e () in 
          empty_f, 
          Star [
            Eq (var, Le_Value (Lv_Loc (Lb_Loc l)));
            ObjFootprint (l, [])
          ]
        | HasField (e1, e2) -> raise (NotImplemented "HasField")
        | Lookup (e1, e2) -> raise (NotImplemented "Lookup")
        | Deallocation (e1, e2) -> raise (NotImplemented "Deallocation")
        | ProtoF (e1, e2) -> raise (NotImplemented "ProtoField")
        | ProtoO (e1, e2) -> raise (NotImplemented "ProtoObj")
      end
    | Mutation m -> raise (NotImplemented "Mutation")