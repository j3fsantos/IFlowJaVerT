open Logic
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