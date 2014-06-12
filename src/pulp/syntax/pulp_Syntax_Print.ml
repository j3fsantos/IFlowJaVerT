open Pulp_Syntax

let string_of_comparison_op x =
  match x with
    | Equal -> "=="

let string_of_bool_op x =
  match x with
    | And -> "&&"
    | Or -> "||"

let string_of_arith_op x =
  match x with
    | Plus -> "+"
    | Minus -> "-"
    | Times -> "*"
    | Div -> "/"

let string_of_bin_op x =
  match x with
    | Comparison op -> string_of_comparison_op op
    | Arith op -> string_of_arith_op op
    | Boolean op -> string_of_bool_op op

let string_of_var x = x

let string_of_codename cn = cn

let string_of_vars xs =
  String.concat "," xs
  
let string_of_formal_params fparams = 
  String.concat "," fparams
  
let string_of_literal lit =
  match lit with
    | Num n -> string_of_float n
    | String x -> Printf.sprintf "\"%s\"" x
    | Null -> "null"
    | Bool b -> string_of_bool b

  
let string_of_builtin_function bf =
  match bf with
    | Sigma x -> Printf.sprintf "Sigma ( %s )" x
    | Gamma x -> Printf.sprintf "Gamma ( %s )" x
    | ObjCoercible x -> Printf.sprintf "ObjCoercible ( %s )" x

let string_of_call c =
  Printf.sprintf "\"%s (@this %s, %s) \"" c.call_name c.call_this (string_of_vars c.call_args)
  
let string_of_ref_type rt =
  match rt with
    | MemberReference -> "Member"
    | VariableReference -> "Variable"
  
let string_of_reference r =
  Printf.sprintf "ref%s(%s, %s)" 
    (string_of_var r.ref_base) 
    (match r.ref_type with
      | MemberReference -> "_o"
      | VariableReference -> "_v"
    ) 
    (string_of_var r.ref_field)
  
let string_of_mutation m =
  Printf.sprintf "[%s] := %s" (string_of_var m.m_left) (string_of_var m.m_right)
  
let string_of_expression e =
  let s = string_of_var in
  match e with
    | Literal l -> string_of_literal l
    | Empty -> "#empty"
    | Var v -> s v
    | BinOp (v1, op, v2) -> Printf.sprintf "%s %s %s" (s v1) (string_of_bin_op op) (s v2)
    | Ref r -> string_of_reference r
    | Lookup v -> Printf.sprintf "[%s]" (s v)
    | Call c -> string_of_call c
    | Fun cn -> Printf.sprintf "function %s" (string_of_codename cn) (* Don't I want formal params here?*) (* I'm confused between function blocks and function expression? *)
    | Obj -> "new ()"
    | BuiltInFunction bf -> string_of_builtin_function bf
  
let rec string_of_statement t =
  let s = string_of_var in
  match t with
    | Skip -> "Skip"
    | Label l -> Printf.sprintf "%s :" l
    | Assignment a -> Printf.sprintf "%s := %s" (s a.assign_left) (string_of_expression a.assign_right)
    | Mutation m -> string_of_mutation m
    | Deallocation v -> Printf.sprintf "delete %s" (s v)
    | Goto ls -> Printf.sprintf "goto %s" (String.concat "," ls)
    | Assume f -> Printf.sprintf "assume %s" (PrintLogic.string_of_formula f)
    | Assert f -> Printf.sprintf "assert %s" (PrintLogic.string_of_formula f)
    | Sugar s -> string_of_sugar s
and string_of_statement_list ts = (String.concat "\n" (List.map string_of_statement ts))
and string_of_sugar t =
  match t with
    | If (condition, thenbranch, elsebranch) -> 
      Printf.sprintf "if (%s) then {\n%s\n}\n else{\n%s\n}\n" 
      (PrintLogic.string_of_formula condition)
      (string_of_statement_list thenbranch)
      (string_of_statement_list elsebranch)
      
let string_of_func_block fb =
   Printf.sprintf "function %s (%s) { \n %s \n}" fb.func_name (string_of_formal_params fb.func_params) (string_of_statement_list fb.func_body)
  