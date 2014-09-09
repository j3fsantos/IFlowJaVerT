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

let string_of_unary_op op =
  match op with
    | Not -> "not"

let string_of_builtin_loc l =
  match l with
    | Lg -> "#lg"
    | Lop -> "#lop"
    | Lfp -> "#lfp"
    | LEval -> "#leval"
    | LRError -> "#lrerror"
    | LTError -> "#lterror"
    | LSError -> "#lserror"
    | LNotImplemented -> "#lnotimplemented"

let string_of_var x = x

let string_of_codename cn = cn

let string_of_vars xs =
  String.concat "," xs
  
let string_of_formal_params fparams = 
  String.concat "," fparams
  
let string_of_literal lit =
  match lit with
    | Loc l -> string_of_builtin_loc l
    | Num n -> string_of_float n
    | String x -> Printf.sprintf "\"%s\"" x
    | Null -> "null"
    | Bool b -> string_of_bool b
    | Undefined -> "#undefined"
    | Empty -> "#empty" 
  
let string_of_ref_type rt =
  match rt with
    | MemberReference -> "Member"
    | VariableReference -> "Variable"

let string_of_pulp_type t =
  match t with
  | NullType -> "Null"
  | UndefinedType -> "Undefined"
  | BooleanType -> "Boolean"
  | StringType -> "String"
  | NumberType -> "Number"
  | ObjectType -> "Object"
  | ReferenceType r ->
    match r with
      | None -> "Reference"
      | Some r -> (string_of_ref_type r)^"Reference" 
  
let rec string_of_expression e =
  let se = string_of_expression in
  match e with
    | Literal l -> string_of_literal l
    | Var v -> string_of_var v
    | BinOp (e1, op, e2) -> Printf.sprintf "%s %s %s" (se e1) (string_of_bin_op op) (se e2)
    | UnaryOp (op, e) -> Printf.sprintf "%s (%s)" (string_of_unary_op op) (se e)
    | IsTypeOf (e, t) -> Printf.sprintf "istypeof (%s, %s)" (se e) (string_of_pulp_type t)
    | Call c -> string_of_call c
    | Ref (e1, e2, t) -> Printf.sprintf "(%s .%s %s)" (se e1)
      (match t with
        | MemberReference -> "_o"
        | VariableReference -> "_v")
      (se e2)
    | Base e -> Printf.sprintf "base (%s)" (se e)
    | Field e -> Printf.sprintf "field (%s)" (se e)
    | Obj -> "new ()"
    | HasField (e1, e2) -> Printf.sprintf "hasfield (%s, %s)" (se e1) (se e2)
    | Lookup (e1, e2) -> Printf.sprintf "[%s.%s]" (se e1) (se e2)
    | Deallocation (e1, e2) -> Printf.sprintf "delete %s.%s" (se e1) (se e2)
    | Pi (l, x) -> Printf.sprintf "Pi ( %s, %s )" (se l) (se x)
and string_of_call c =
  let se = string_of_expression in
  let ses xs = String.concat "," (List.map se xs) in
  Printf.sprintf "%s (%s, %s, %s)" (se c.call_name) (se c.call_this) (se c.call_scope) (ses c.call_args)
  
  
let string_of_mutation m =
  let se = string_of_expression in
  Printf.sprintf "[%s.%s] := %s" (se m.m_loc) (se m.m_field) (se m.m_right)
  
let rec string_of_statement t =
  let s = string_of_var in
  match t with
    | Skip -> "Skip"
    | Label l -> Printf.sprintf "label %s" l
    | Goto s -> Printf.sprintf "goto %s" s
    | GuardedGoto (e, s1, s2) -> Printf.sprintf "goto [%s] %s, %s" (string_of_expression e) s1 s2
    | Assume e -> Printf.sprintf "Assume %s" (string_of_expression e)
    | Assert e -> Printf.sprintf "Assert %s" (string_of_expression e)
    | Assignment a -> Printf.sprintf "%s := %s" (s a.assign_left) (string_of_expression a.assign_right)
    | Mutation m -> string_of_mutation m
    | Sugar s -> string_of_sugar s
and string_of_statement_list ts = (String.concat "\n" (List.map string_of_statement ts))
and string_of_sugar t =
  match t with
    | If (condition, thenbranch, elsebranch) -> 
      Printf.sprintf "if (%s) then {\n%s\n}\n else{\n%s\n}\n" 
      (string_of_expression condition)
      (string_of_statement_list thenbranch)
      (string_of_statement_list elsebranch)
      
  
let string_of_ctx_vars v = 
  Printf.sprintf "%s : [%s]" v.func_id (string_of_vars v.fun_bindings)
  
let string_of_returs_throws ctx =
  Printf.sprintf "[end: variable %s label %s; return: variable %s label %s; throw: variable %s label %s]" 
  ctx.end_var
  ctx.label_end
  ctx.return_var
  ctx.label_return
  ctx.throw_var
  ctx.label_throw 
      
let string_of_env_var ctx = 
  Printf.sprintf "\n env variables %s \n \n \n " 
  (String.concat ";" (List.map string_of_ctx_vars ctx.env_vars))

let string_of_func_block fb =
   Printf.sprintf "procedure %s (%s) %s { \n %s \n} \n with context %s \n \n \n" 
   fb.func_name 
   (string_of_formal_params fb.func_params) 
   (string_of_returs_throws fb.func_ctx)
   (string_of_statement_list fb.func_body) 
   (string_of_env_var fb.func_ctx)