open Pulp_Syntax
open Pulp_Syntax_Utils
open Pulp_Procedure

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

let string_of_bitwise_op x =
  match x with
    | BitwiseAnd -> "&"
    | BitwiseOr -> "^"
    | BitwiseXor -> "|"
    | LeftShift -> "<<"
    | SignedRightShift -> ">>"
    | UnsignedRightShift -> ">>>"

let string_of_bin_op x =
  match x with
    | Concat -> "^"
    | Comparison op -> string_of_comparison_op op
    | Arith op -> string_of_arith_op op
    | Boolean op -> string_of_bool_op op
    | Bitwise op -> string_of_bitwise_op op

let string_of_unary_op op =
  match op with
    | Not -> "not"
    | Negative -> "-"
    | ToStringOp -> "num_to_string"
    | ToNumberOp -> "string_to_num"
    | ToInt32Op -> "num_to_int32"
    | ToUint32Op -> "num_to_unit32"
    | BitwiseNot -> "!"

let string_of_feature f =
  match f with
    | GetValuePrim -> "getvalueprim"
    | ToNumber -> "tonumber"
    | ToString -> "tostring"
    | ToObject -> "toobject"

let string_of_builtin_loc l =
  match l with
    | Lg -> "#lg"
    | Lg_isNaN -> "#lg_isNan"
    | Lg_isFinite -> "#lg_isFinite"
    | Lop -> "#lop"
    | Lop_toString -> "#lop_toString"
    | Lop_valueOf -> "#lop_valueOf"
    | Lop_isPrototypeOf -> "#lop_isPrototypeOf"
    | LFunction -> "#lfunction"
    | Lfp -> "#lfp"
    | LEval -> "#leval"
    | LError -> "#lerror"
    | Lep -> "#lep"
    | LRError -> "#lrerror"
    | Lrep -> "#lrep"
    | LTError -> "#lterror"
    | Ltep -> "#ltep"
    | LSError -> "#lserror"
    | Lsep -> "#lsep"
    | LObject -> "#lobject"
    | LObjectGetPrototypeOf -> "#lobject_get_prototype_of"
    | LBoolean -> "#lboolean"
    | Lbp -> "#lbp"
    | Lbp_toString -> "#lbp_toString"
    | Lbp_valueOf -> "#lbp_valueOf"
    | LNumber -> "#lnumber"
    | Lnp -> "#lnp"
    | Lnp_toString -> "#lnp_toString"
    | Lnp_valueOf -> "#lnp_valueOf"
    | LMath -> "#lmath"
    | LString -> "#lstring"
    | Lsp -> "#lsp"
    | Lsp_toString -> "#lsp_toString"
    | Lsp_valueOf -> "#lsp_valueOf"
    | LArray -> "#larray"
    | LArrayp -> "#larrayp"
    | LDate -> "#ldate"
    | Ldp -> "#ldp"
    | LRegExp -> "#lregexp"
    | LRegExpP -> "#lregexpp"
    | LJSON -> "#ljson"
    | LNotImplemented f -> "#lnotimplemented_" ^ (string_of_feature f)
    | LStub s -> "#lstub##" ^ s

let string_of_builtin_loc_no_hash l =
  let s = string_of_builtin_loc l in
  String.sub s 1 (String.length s - 1)

let string_of_builtin_function f =
  match f with
    | Global_isNaN -> "#global_is_nan"
    | Global_isFinite -> "#global_is_finite"
    | Boolean_Call -> "#boolean_call"
    | Boolean_Construct -> "#boolean_construct"
    | Boolean_Prototype_toString -> "#boolean_prototype_to_string"
    | Boolean_Prototype_valueOf -> "#boolean_prototype_value_of"
    | Object_Call -> "#object_call"
    | Object_Construct -> "#object_construct"
    | Object_Prototype_toString -> "#object_prototype_to_string"
    | Object_Prototype_valueOf -> "#object_prototype_value_of"
    | Object_Prototype_isPrototypeOf -> "#object_prototype_is_prototype_of"
    | Object_getPrototypeOf -> "#object_get_prototype_of"
    | Number_Call -> "#number_call"
    | Number_Construct -> "#number_construct"
    | Number_Prototype_toString -> "#number_prototype_to_string"
    | Number_Prototype_valueOf -> "#number_prototype_value_of"
    | String_Call -> "#string_call"
    | String_Construct -> "#string_construct"
    | String_Prototype_toString -> "#string_prototype_to_string"
    | String_Prototype_valueOf -> "#string_prototype_value_of"
    | TypeError_Call -> "#terror_call"
    | TypeError_Construct -> "#terror_construct"
    | ReferenceError_Call -> "#rerror_call"
    | ReferenceError_Construct -> "#rerror_construct"
    | SyntaxError_Call -> "#serror_call"
    | SyntaxError_Construct -> "#serror_construct"
    | Function_Call -> "#function_call"
    | Function_Construct -> "#function_construct"
    | Function_Prototype_Call -> "#function_protottype_call"
    | Not_Implemented_Stub s -> "#not_implemented_stub##" ^ s

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
  | ObjectType (Some Normal) -> "Normal Object"
  | ObjectType None -> "Object"
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

let string_of_spec_fun_id sf =
  match sf with
    | GetValue _ -> "#GetValue"
    | PutValue _ -> "#PutValue"
    | Get _ -> "#[[Get]]"
    | HasProperty _ -> "#[[HasProperty]]"
    | DefaultValue _ -> "#[[DefaultValue]]"
    | ToPrimitive _ -> "#ToPrimitive"
    | ToBoolean _ -> "#ToBoolean"
    | ToNumber _ -> "#ToNumber"
    | ToNumberPrim _ -> "#ToNumberPrim"
    | ToString _ -> "#ToString"
    | ToStringPrim _ -> "#ToStringPrim"
    | ToObject _ -> "#ToObject"
    | CheckObjectCoercible _ -> "#CheckObjectCoercible" 
    | IsCallable _ -> "#IsCallable"
    | AbstractEquality _ -> "#AbstractEquality"
    | StrictEquality _ -> "#StrictEquality"
    | StrictEqualitySameType _ -> "#StrictEqualitySameType"

let string_of_spec_function sf =
  let f = string_of_expression in
  let id = string_of_spec_fun_id sf in
  match sf with
    | GetValue e -> Printf.sprintf "%s(%s)" id (f e)
    | PutValue (e1, e2) -> Printf.sprintf "%s(%s, %s)" id (f e1) (f e2)
    | Get (e1, e2) -> Printf.sprintf "%s(%s, %s)" id (f e1) (f e2)
    | HasProperty (e1, e2) -> Printf.sprintf "%s(%s, %s)" id (f e1) (f e2)
    | DefaultValue (e, pt) -> Printf.sprintf "%s(%s, %s)" id (f e) (match pt with None -> "" | Some pt -> string_of_pulp_type pt)
    | ToPrimitive (e, pt) -> Printf.sprintf "%s(%s, %s)" id (f e)  (match pt with None -> "" | Some pt -> string_of_pulp_type pt)
    | ToBoolean e -> Printf.sprintf "%s(%s)" id (f e)
    | ToNumber e -> Printf.sprintf "%s(%s)" id (f e)
    | ToNumberPrim e -> Printf.sprintf "%s(%s)" id (f e)
    | ToString e -> Printf.sprintf "%s(%s)" id (f e)
    | ToStringPrim e -> Printf.sprintf "%s(%s)" id (f e)
    | ToObject e -> Printf.sprintf "%s(%s)" id (f e)
    | CheckObjectCoercible e -> Printf.sprintf "%s(%s)" id (f e)
    | IsCallable e -> Printf.sprintf "%s(%s)" id (f e)
    | AbstractEquality (e1, e2, b) -> Printf.sprintf "%s(%s, %s, %b)" id (f e1) (f e2) b
    | StrictEquality (e1, e2) -> Printf.sprintf "%s(%s, %s)" id (f e1) (f e2)
    | StrictEqualitySameType (e1, e2) -> Printf.sprintf "%s(%s, %s)" id (f e1) (f e2)
 
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
    | SpecFunction (v, sf, excel_label) -> Printf.sprintf "%s = %s with (%s)" 
      v (string_of_spec_function sf) excel_label
      
  
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
  
let string_of_break_continue_labels ctx =
  Printf.sprintf "\n break labels %s \n continue labels %s \n " 
  (String.concat ";" (List.map (fun (l1, l2) -> "(" ^ l1 ^ "," ^ l2 ^ ")") ctx.label_break))
  (String.concat ";" (List.map (fun (l1, l2) -> "(" ^ l1 ^ "," ^ l2 ^ ")") ctx.label_continue))

let string_of_func_block fb =
   Printf.sprintf "procedure %s (%s) %s { \n %s \n} \n with context %s \n" 
   fb.func_name 
   (string_of_formal_params fb.func_params) 
   (string_of_returs_throws fb.func_ctx)
   (string_of_statement_list fb.func_body) 
   (string_of_env_var fb.func_ctx)
  
let string_of_all_functions p_exp =
  AllFunctions.fold (fun fid fwc content -> content ^ Printf.sprintf "%s \n" (string_of_func_block fwc)) p_exp ""
  
let string_of_functions p_exp fs =
  let p_exp = AllFunctions.filter (fun fid fwc -> List.mem fid fs) p_exp in
  AllFunctions.fold (fun fid fwc content -> Printf.printf "%s\n" fid; content ^ Printf.sprintf "%s \n" (string_of_func_block fwc)) p_exp ""
