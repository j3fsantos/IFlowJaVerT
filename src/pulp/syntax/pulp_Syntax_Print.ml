open Pulp_Syntax
open Pulp_Syntax_Utils

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
    | Undefined -> "#undefined"
    | Empty -> "#empty" 

let string_of_call c =
  Printf.sprintf "%s (%s, %s, %s)" c.call_name c.call_this c.call_scope (string_of_vars c.call_args)
  
let string_of_ref_type rt =
  match rt with
    | MemberReference -> "Member"
    | VariableReference -> "Variable"
  
let string_of_reference r =
  Printf.sprintf "(%s .%s %s)"  
    (string_of_var r.ref_base)
    (match r.ref_type with
      | MemberReference -> "_o"
      | VariableReference -> "_v"
    ) 
    (string_of_var r.ref_field)
  
let string_of_mutation m =
  Printf.sprintf "[%s.%s] := %s" (string_of_var m.m_loc) (string_of_var m.m_field) (string_of_var m.m_right)
  
let string_of_expression e =
  let s = string_of_var in
  match e with
    | Literal l -> string_of_literal l
    | Var v -> s v
    | BinOp (v1, op, v2) -> Printf.sprintf "%s %s %s" (s v1) (string_of_bin_op op) (s v2)
    | Call c -> string_of_call c
    | Ref r -> string_of_reference r
    | Base v -> Printf.sprintf "base (%s)" (s v)
    | Field v -> Printf.sprintf "field (%s)" (s v)
    | Obj -> "new ()"
    | HasField (v1, v2) -> Printf.sprintf "hasfield (%s, %s)" (s v1) (s v2)
    | Lookup (v1, v2) -> Printf.sprintf "[%s.%s]" (s v1) (s v2)
    | Deallocation (v1, v2) -> Printf.sprintf "Delete %s.%s" (s v1) (s v2)
    | Pi (l, x) -> Printf.sprintf "Pi ( %s, %s )" l x
  
let rec string_of_statement t =
  let s = string_of_var in
  match t with
    | Skip -> "Skip"
    | Label l -> Printf.sprintf "label %s" l
    | Goto ls -> Printf.sprintf "goto %s" (String.concat "," ls)
    | Assume f -> Printf.sprintf "assume %s" (PrintLogic.string_of_formula f)
    | Assert f -> Printf.sprintf "assert %s" (PrintLogic.string_of_formula f)
    | Assignment a -> Printf.sprintf "%s := %s" (s a.assign_left) (string_of_expression a.assign_right)
    | Mutation m -> string_of_mutation m
    | Sugar s -> string_of_sugar s
and string_of_statement_list ts = (String.concat "\n" (List.map string_of_statement ts))
and string_of_sugar t =
  match t with
    | If (condition, thenbranch, elsebranch) -> 
      Printf.sprintf "If (%s) Then {\n%s\n}\n Else{\n%s\n}\n" 
      (PrintLogic.string_of_formula condition)
      (string_of_statement_list thenbranch)
      (string_of_statement_list elsebranch)
      
  
let string_of_ctx_vars v = 
  Printf.sprintf "%s : [%s]" v.func_id (string_of_vars v.fun_bindings)
      
let string_of_translation_ctx ctx = 
  Printf.sprintf "\n env variables %s \n return var %s return label %s exception var %s exception label %s \n \n \n" 
  (String.concat ";" (List.map string_of_ctx_vars ctx.env_vars))
  ctx.return_var
  ctx.label_return
  ctx.throw_var
  ctx.label_throw 
      
let string_of_func_block fb =
   Printf.sprintf "function %s (%s) { \n %s \n} \n with context %s \n \n \n" 
   fb.func_name 
   (string_of_formal_params fb.func_params) 
   (string_of_statement_list fb.func_body) 
   (string_of_translation_ctx fb.func_ctx)