open Batteries
open List
open Pulp_Logic
open Pulp_Syntax_Print
open Pulp_Syntax

let string_of_logical_var x =
  match x with
    | AVar x -> Printf.sprintf "?%s" x
    | EVar x -> Printf.sprintf "_%s" x
  
let string_of_var x = x

let string_of_variable_types x =
  match x with
    | LogicalVariable x -> string_of_logical_var x
    | ProgramVariable x -> string_of_var x

let string_of_codename x = x
      
let rec string_of_logical_exp x =
  match x with
    | Le_Literal x -> string_of_literal x
    | Le_PVar x -> string_of_var x
    | Le_Var x -> string_of_logical_var x
    | Le_None -> "#(/)"
    | Le_BinOp (x, op, y) -> Printf.sprintf "(%s %s %s)" (string_of_logical_exp x) 
                             (string_of_bin_op op) (string_of_logical_exp y)
    | Le_Ref (x, y, rt) -> Printf.sprintf "ref(%s,%s,%s)" 
                           (string_of_logical_exp x) (string_of_logical_exp y) (string_of_ref_type rt)
    | Le_Base e -> Printf.sprintf "#base (%s)" (string_of_logical_exp e)
    | Le_Field e -> Printf.sprintf "#field (%s)" (string_of_logical_exp e)
    | Le_TypeOf e -> Printf.sprintf "#typeOf (%s)" (string_of_logical_exp e)
    | Le_UnOp (op, e) -> Printf.sprintf "(%s %s)" (string_of_unary_op op) (string_of_logical_exp e) 

let string_of_val_var_pair (x,y) = (string_of_var x) ^ ":" ^ (string_of_logical_exp y)

let rec get_non_empty_heaplets_for_expr e f =
  let rec inner f fields =
      match f with
        | Star fl -> fold_left (fun vl f -> (inner f vl)) fields fl
        | Heaplet (_, _, Le_None) -> fields
        | Heaplet (e1, e2, e3) -> if (e1 = e) then (ExpMap.add e2 e3 fields) else fields 
        | _ -> fields in
   inner f ExpMap.empty
      
let rec get_empty_heaplets_for_expr e f =
  match f with 
    | Star fl -> fold_left (fun vl f -> unique (vl @ (get_empty_heaplets_for_expr e f))) [] fl
    | Heaplet (e1, e2, Le_None) -> if (e = e1) then [e2] else []
    | _ -> []

let string_of_pi pi = 
  let fe = string_of_logical_exp in
  Printf.sprintf "#pi (%s, %s, %s, %s, %s)" 
    (fe pi.pi_list)
    (fe pi.pi_obj)
    (fe pi.pi_field)
    (fe pi.pi_loc)
    (fe pi.pi_value)
    
let rec string_of_formula x =
  let fe = string_of_logical_exp in
  match x with
    | Star l -> "  " ^ String.concat "\n* " (map (Printf.sprintf "(%s)") (map string_of_formula l))
    | Heaplet (e1, e2, e3) -> Printf.sprintf "%s.%s |-> %s" (fe e1) (fe e2) (fe e3)
    | Eq (x, y) -> Printf.sprintf "%s = %s" (fe x) (fe y)
    | NEq (x, y) -> Printf.sprintf "%s != %s" (fe x) (fe y)
    | REq x -> Printf.sprintf "#r = %s" (fe x)
    | ObjFootprint (e, es) -> Printf.sprintf "#footprint [%s] (%s)" (fe e) 
        (String.concat "," (map fe es))
    | Pi p -> string_of_pi p 
        
let rec string_of_fields hasnt has = 
  Printf.sprintf "(%s | %s)" 
  (String.concat ", " (map string_of_logical_exp hasnt))
  (String.concat ", " 
   (List.map (fun (f, v) -> Printf.sprintf "%s : %s" 
    (string_of_logical_exp f)
    (string_of_logical_exp v)
  ) (ExpMap.bindings has)))


