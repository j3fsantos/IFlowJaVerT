open Pulp_Syntax
open Pulp_Syntax_Utils

let string_of_comparison_op x =
  match x with
    | Equal -> "="
    | LessThan -> "<"

let string_of_bool_op x =
  match x with
    | And -> "and"
    | Or -> "or"

let string_of_arith_op x =
  match x with
    | Plus -> "+"
    | Minus -> "-"
    | Times -> "*"
    | Div -> "/"
    | Mod -> "%"

let string_of_bin_op x =
  match x with
    | Concat -> "^"
    | Comparison op -> string_of_comparison_op op
    | Arith op -> string_of_arith_op op
    | Boolean op -> string_of_bool_op op

let string_of_unary_op op =
  match op with
    | Not -> "not"
    | Negative -> "-"
    | ToStringOp -> "num_to_string"
    | ToNumberOp -> "string_to_num"

let string_of_feature f =
  match f with
    | GetValuePrim -> "getvalueprim"
    | ToNumber -> "tonumber"
    | ToString -> "tostring"

let string_of_builtin_loc l =
  match l with
    | Lg -> "#lg"
    | Lop -> "#lop"
    | Lfp -> "#lfp"
    | LEval -> "#leval"
    | LRError -> "#lrerror"
    | LTError -> "#lterror"
    | LSError -> "#lserror"
    | LObject -> "#lobject"
    | LNotImplemented f -> "#lnotimplemented_" ^ (string_of_feature f)

let string_of_builtin_field f =
  match f with
    | FProto -> "#proto"
    | FId -> "#fid"
    | FScope -> "#scope"
    | FPrototype -> "prototype"

let string_of_var x = x

let string_of_codename cn = cn

let string_of_vars xs =
  String.concat "," xs
  
let string_of_formal_params fparams = 
  String.concat "," fparams
  
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
  | ObjectType (Some Builtin) -> "Builtin Object"
  | ObjectType _ -> "Object"
  | ReferenceType r ->
    match r with
      | None -> "Reference"
      | Some r -> (string_of_ref_type r)^"Reference"
  
let string_of_literal lit =
  match lit with
    | LLoc l -> string_of_builtin_loc l
    | Num n -> string_of_float n
    | String x -> Printf.sprintf "\"%s\"" x
    | Null -> "null"
    | Bool b -> string_of_bool b
    | Undefined -> "#undefined"
    | Empty -> "#empty" 
    | Type t -> string_of_pulp_type t 
  
let rec string_of_expression e =
  let se = string_of_expression in
  match e with
    | Literal l -> string_of_literal l
    | Var v -> string_of_var v
    | BinOp (e1, op, e2) -> Printf.sprintf "%s %s %s" (se e1) (string_of_bin_op op) (se e2)
    | UnaryOp (op, e) -> Printf.sprintf "%s (%s)" (string_of_unary_op op) (se e)
    | IsTypeOf (e, t) -> Printf.sprintf "typeOf (%s) = %s" (se e) (string_of_pulp_type t)
    | TypeOf e -> Printf.sprintf "typeOf (%s)" (se e) 
    | Ref (e1, e2, t) -> Printf.sprintf "ref(%s,%s,%s)" (se e1) (se e2)
      (match t with
        | MemberReference -> "o"
        | VariableReference -> "v")
    | Base e -> Printf.sprintf "base (%s)" (se e)
    | Field e -> Printf.sprintf "field (%s)" (se e)

let string_of_call c =
  let se = string_of_expression in
  let ses xs = String.concat "," (List.map se xs) in
  Printf.sprintf "%s (%s, %s, %s) with %s" (se c.call_name) (se c.call_this) (se c.call_scope) (ses c.call_args) (c.call_throw_label)
 
let string_of_eval c =
  let se = string_of_expression in
  let ses xs = String.concat "," (List.map se xs) in
  Printf.sprintf "eval (%s, %s, %s) with %s" (se c.call_this) (se c.call_scope) (ses c.call_args) (c.call_throw_label)

let string_of_assign_right aer =
  let se = string_of_expression in
  match aer with
    | Expression e -> se e
    | Call c -> string_of_call c
    | Eval c -> string_of_eval c
    | BuiltinCall c -> string_of_call c
    | Obj -> "new ()"
    | HasField (e1, e2) -> Printf.sprintf "hasField (%s, %s)" (se e1) (se e2)
    | Lookup (e1, e2) -> Printf.sprintf "[%s,%s]" (se e1) (se e2)
    | Deallocation (e1, e2) -> Printf.sprintf "delete (%s,%s)" (se e1) (se e2)
    | ProtoF (l, x) -> Printf.sprintf "proto_field ( %s, %s )" (se l) (se x)
    | ProtoO (l, x) -> Printf.sprintf "proto_obj ( %s, %s )" (se l) (se x)
  
let string_of_mutation m =
  let se = string_of_expression in
  Printf.sprintf "[%s,%s] := %s" (se m.m_loc) (se m.m_field) (se m.m_right)
  
let string_of_basic_statement bs =
  match bs with
    | Skip -> "Skip"
    | Assignment a -> Printf.sprintf "%s := %s" (string_of_var a.assign_left) (string_of_assign_right a.assign_right)
    | Mutation m -> string_of_mutation m
 
let rec string_of_statement t =
  match t with
    | Label l -> Printf.sprintf "label %s" l
    | Goto s -> Printf.sprintf "goto %s" s
    | GuardedGoto (e, s1, s2) -> Printf.sprintf "goto [%s] %s, %s" (string_of_expression e) s1 s2
    | Basic bs -> string_of_basic_statement bs
    | Sugar s -> string_of_sugar s
and string_of_statement_list ts = String.concat "\n" 
 (List.mapi (fun i t -> (string_of_int i) ^ ". " ^ (string_of_statement t)) ts)
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
  Printf.sprintf "[return: variable %s label %s; throw: variable %s label %s]" 
  ctx.return_var
  ctx.label_return
  ctx.throw_var
  ctx.label_throw 
      
let string_of_env_var ctx = 
  Printf.sprintf "\n env variables %s \n \n \n " 
  (String.concat ";" (List.map string_of_ctx_vars ctx.env_vars))

let string_of_func_block fb =
   Printf.sprintf "procedure %s (%s) %s { \n %s \n} \n with context %s \n" 
   fb.func_name 
   (string_of_formal_params fb.func_params) 
   (string_of_returs_throws fb.func_ctx)
   (string_of_statement_list fb.func_body) 
   (string_of_env_var fb.func_ctx)
  
let string_of_all_functions p_exp =
  AllFunctions.fold (fun fid fwc content -> content ^ Printf.sprintf "%s \n" (string_of_func_block fwc)) p_exp ""