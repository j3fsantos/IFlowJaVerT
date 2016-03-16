(* ./src/pulp/syntax/pulp_Syntax_Print.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open Pulp_Syntax
open Pulp_Syntax_Utils
open Pulp_Procedure

let string_of_comparison_op x =
  match x with
    | Equal -> "="
    | LessThan -> "<"
    | LessThanEqual -> "<="

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
    | Subtype -> "<:"
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
    | LEvalError -> "#levalerror"
    | LEvalErrorP -> "#levalerrorp"
    | LRangeError -> "#lrangeerror"
    | LRangeErrorP -> "#lrangeerrorp"
    | LURIError -> "#lurierror"
    | LURIErrorP -> "#lurierrorp"
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
    | LJSON -> "#ljson"
    | LNotImplemented f -> "#lnotimplemented_" ^ (string_of_feature f)
    | LStub s -> "#lstub##" ^ s

let string_of_builtin_loc_no_hash l =
  let s = string_of_builtin_loc l in
  String.sub s 1 (String.length s - 1)

let string_of_builtin_function f =
  match f with
    | Global_eval -> "eval"
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
    | Error_Call_Construct -> "#error_call_construct"
    | TypeError_Call_Construct -> "#terror_call_construct"
    | ReferenceError_Call_Construct -> "#rerror_call_construct"
    | SyntaxError_Call_Construct -> "#serror_call_construct"
    | EvalError_Call_Construct -> "#evalerror_call_construct"
    | RangeError_Call_Construct -> "#rangeerror_call_construct"
    | URIError_Call_Construct -> "#urierror_call_construct"
    | Function_Call -> "#function_call"
    | Function_Construct -> "#function_construct"
    | Function_Prototype_Call -> "#function_protottype_call"
    | Not_Implemented_Stub s -> "#not_implemented_stub##" ^ s

let rec tabs_to_str i  = 
	if i == 0 then "" else "\t" ^ (tabs_to_str (i - 1))

let string_of_var x = x

let string_of_codename cn = cn

let string_of_vars xs =
  String.concat "," xs
  
let string_of_formal_params fparams = 
  String.concat "," fparams

let sexpr_of_formal_params fparams = 
	List.fold_left 
		(fun prev_params param -> 
			prev_params ^ " '" ^ param)  
		""
		fparams				
		  
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

let rec sexpr_of_expression e =
  let se = sexpr_of_expression in
  match e with
    | Literal l -> string_of_literal l
    | Var v -> "'" ^ string_of_var v
		(* (bop e1 e2) *)
    | BinOp (e1, op, e2) -> Printf.sprintf "(%s %s %s)" (string_of_bin_op op) (se e1) (se e2)
		(* (uop e1 e2) *)
    | UnaryOp (op, e) -> Printf.sprintf "(%s %s)" (string_of_unary_op op) (se e)
		(* ('typeof e) *)
    | TypeOf e -> Printf.sprintf "('typeOf %s)" (se e) 
		(* ('ref e1 e2 e3) *)
    | Ref (e1, e2, t) -> Printf.sprintf "('ref %s %s %s)" (se e1) (se e2)
      (match t with
        | MemberReference -> "'o"
        | VariableReference -> "'v")
		(* ('base e) *)
    | Base e -> Printf.sprintf "('base %s)" (se e)
		(* ('field e) *)
    | Field e -> Printf.sprintf "('field %s)" (se e)


let string_of_call c =
  let se = string_of_expression in
  let ses xs = String.concat "," (List.map se xs) in
  Printf.sprintf "%s (%s, %s, %s) with %s" (se c.call_name) (se c.call_this) (se c.call_scope) (ses c.call_args) (c.call_throw_label)

let sexpr_of_call left_var_str c i line_numbers_on =
	(* ('call var e (e1 ... en) i) *)
	let str_i = string_of_int i in 
  let se = sexpr_of_expression in
  let ses xs = match xs with 
		| [] -> ""
		| _ -> " " ^ String.concat " " (List.map se xs) in
	if (line_numbers_on) 
		then Printf.sprintf "(%s 'call %s %s (%s %s%s) %s)" str_i left_var_str (se c.call_name) (se c.call_this) (se c.call_scope) (ses c.call_args) (c.call_throw_label)
		else Printf.sprintf "('call %s %s (%s %s%s) %s)" left_var_str (se c.call_name) (se c.call_this) (se c.call_scope) (ses c.call_args) (c.call_throw_label)

let sexpr_of_scall left_var_str c i line_numbers_on =
	let str_i = string_of_int i in 
  let se = sexpr_of_expression in
  let ses xs = match xs with 
		| [] -> ""
		| _ -> " " ^ String.concat " " (List.map se xs) in
	if (line_numbers_on) 
		then Printf.sprintf "(%s 'call %s %s (%s %s%s) %s)" str_i left_var_str (se c.scall_name) (se c.scall_this) (se c.scall_scope) (ses c.scall_args) (string_of_int c.scall_throw_label)
		else Printf.sprintf "('call %s %s (%s %s%s) %s)" left_var_str (se c.scall_name) (se c.scall_this) (se c.scall_scope) (ses c.scall_args) (string_of_int c.scall_throw_label)

let string_of_eval c =
  let se = sexpr_of_expression in
  let ses xs = String.concat "," (List.map se xs) in
  Printf.sprintf "eval (%s, %s, %s) with %s" (se c.call_this) (se c.call_scope) (ses c.call_args) (c.call_throw_label)

let sexpr_of_eval left_var_str c i line_numbers_on  =
	let str_i = string_of_int i in 
  let se = string_of_expression in
  let ses xs = match xs with 
		| [] -> ""
		| _ -> " " ^ String.concat " " (List.map se xs) in
	if (line_numbers_on) 
		then Printf.sprintf "(%s 'call 'eval %s (%s %s%s) %s)" str_i left_var_str (se c.call_this) (se c.call_scope) (ses c.call_args) (c.call_throw_label)
		else Printf.sprintf "('call 'eval %s (%s %s%s) %s)" left_var_str (se c.call_this) (se c.call_scope) (ses c.call_args) (c.call_throw_label)

let sexpr_of_seval left_var_str c i line_numbers_on  =
	let str_i = string_of_int i in 
  let se = string_of_expression in
  let ses xs = match xs with 
		| [] -> ""
		| _ -> " " ^ String.concat " " (List.map se xs) in
	if (line_numbers_on) 
		then Printf.sprintf "(%s 'call 'eval %s (%s %s%s) %s)" str_i left_var_str (se c.scall_this) (se c.scall_scope) (ses c.scall_args) (string_of_int c.scall_throw_label)
		else Printf.sprintf "('call 'eval %s (%s %s%s) %s)" left_var_str (se c.scall_this) (se c.scall_scope) (ses c.scall_args) (string_of_int c.scall_throw_label)

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
		| _ -> "illegal_construct()"

let sexpr_of_assign_right left_var_str aer i line_numbers_on =
  let se = sexpr_of_expression in
	let str_i = string_of_int i in 
  match aer with
	  (* ('var_assign var e1 e2) *)
    | Expression e -> 
				if (line_numbers_on)
					then Printf.sprintf "(%s 'var_assign %s %s)" str_i left_var_str (se e)
					else Printf.sprintf "('var_assign %s %s)" left_var_str (se e)
		(* calls *)
    | Call c -> sexpr_of_call left_var_str c i line_numbers_on 
    | Eval c -> sexpr_of_eval left_var_str c i line_numbers_on 
    | BuiltinCall c -> sexpr_of_call left_var_str c i line_numbers_on 
		| SCall c -> sexpr_of_scall left_var_str c i line_numbers_on 
    | SEval c -> sexpr_of_seval left_var_str c i line_numbers_on 
    | SBuiltinCall c -> sexpr_of_scall left_var_str c i line_numbers_on 
		(* end calls*)
		(* ('new var) *)
    | Obj -> 
				if (line_numbers_on)
					then Printf.sprintf "('new %s)" left_var_str
					else Printf.sprintf "('new %s)" left_var_str
		(* ('hasField var e1 e2) *)
    | HasField (e1, e2) -> 
			  if (line_numbers_on)
					then Printf.sprintf "(%s 'hasField %s %s %s)" str_i left_var_str (se e1) (se e2)
					else Printf.sprintf "('hasField %s %s %s)" left_var_str (se e1) (se e2)	
    (* ('lookup var e1 e2) *)
		| Lookup (e1, e2) -> 
				if (line_numbers_on)
					then Printf.sprintf "(%s 'lookup %s %s %s)"str_i left_var_str (se e1) (se e2)
					else Printf.sprintf "('lookup %s %s %s)" left_var_str (se e1) (se e2)
		(* ('delete var e1 e2) *)
    | Deallocation (e1, e2) -> 
				if (line_numbers_on) 
					then Printf.sprintf "(%s 'delete %s %s %s)" str_i left_var_str (se e1) (se e2)
					else Printf.sprintf "('delete %s %s %s)" left_var_str (se e1) (se e2)
		(* ('proto_field var e1 e2) *)
    | ProtoF (l, x) -> 
				if (line_numbers_on) 
					then Printf.sprintf "(%s 'proto_field %s %s %s )" str_i left_var_str (se l) (se x)
					else Printf.sprintf "('proto_field %s %s %s )" left_var_str (se l) (se x)
		(* ('proto_obj var e1 e2) *)
    | ProtoO (l, x) -> 
				if (line_numbers_on) 
					then Printf.sprintf "(%s 'proto_obj %s %s %s)" str_i left_var_str (se l) (se x)
					else Printf.sprintf "('proto_obj %s %s %s)" left_var_str (se l) (se x)

let string_of_mutation m =
  let se = string_of_expression in
  Printf.sprintf "[%s,%s] := %s" (se m.m_loc) (se m.m_field) (se m.m_right)

let sexpr_of_mutation m i line_numbers_on =
	(* ('mutation var e e) *)
  let se = sexpr_of_expression in
	let str_i = string_of_int i in 
	if (line_numbers_on) 
		then Printf.sprintf "(%s 'mutation %s %s %s)" str_i (se m.m_loc) (se m.m_field) (se m.m_right)
		else Printf.sprintf "('mutation %s %s %s)" (se m.m_loc) (se m.m_field) (se m.m_right)
	
let string_of_basic_statement bs =
  match bs with
    | Skip -> "Skip"
    | Assignment a -> Printf.sprintf "%s := %s" (string_of_var a.assign_left) (string_of_assign_right a.assign_right)
    | Mutation m -> string_of_mutation m

let sexpr_of_basic_statement bs i line_numbers_on =
	let str_i = string_of_int i in 
  match bs with
	  (* ('skip) *)
    | Skip -> 
				if (line_numbers_on) 
					then Printf.sprintf "(%s 'skip)" str_i
					else "('skip)"
    | Assignment a -> (sexpr_of_assign_right ("'" ^ (string_of_var a.assign_left)) a.assign_right i line_numbers_on)
    | Mutation m -> (sexpr_of_mutation m i line_numbers_on)

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
    | AbstractRelation _ -> "#AbstractRelation"
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
    | AbstractRelation (e1, e2, b) -> Printf.sprintf "%s(%s, %s, %b)" id (f e1) (f e2) b
    | StrictEquality (e1, e2) -> Printf.sprintf "%s(%s, %s)" id (f e1) (f e2)
    | StrictEqualitySameType (e1, e2) -> Printf.sprintf "%s(%s, %s)" id (f e1) (f e2)

let sexpr_of_spec_function sf =
  let f = sexpr_of_expression in
  match sf with
    | GetValue e -> Printf.sprintf "(%s)" (f e)
    | PutValue (e1, e2) -> Printf.sprintf "(%s %s)" (f e1) (f e2)
    | Get (e1, e2) -> Printf.sprintf "(%s %s)" (f e1) (f e2)
    | HasProperty (e1, e2) -> Printf.sprintf "(%s %s)" (f e1) (f e2)
    | DefaultValue (e, pt) -> Printf.sprintf "(%s %s)" (f e) (match pt with None -> "" | Some pt -> string_of_pulp_type pt)
    | ToPrimitive (e, pt) -> Printf.sprintf "(%s %s)" (f e)  (match pt with None -> "" | Some pt -> string_of_pulp_type pt)
    | ToBoolean e -> Printf.sprintf "(%s)" (f e)
    | ToNumber e -> Printf.sprintf "(%s)" (f e)
    | ToNumberPrim e -> Printf.sprintf "(%s)" (f e)
    | ToString e -> Printf.sprintf "(%s)" (f e)
    | ToStringPrim e -> Printf.sprintf "(%s)" (f e)
    | ToObject e -> Printf.sprintf "(%s)" (f e)
    | CheckObjectCoercible e -> Printf.sprintf "(%s)" (f e)
    | IsCallable e -> Printf.sprintf "(%s)" (f e)
    | AbstractRelation (e1, e2, b) -> Printf.sprintf "(%s %s %b)" (f e1) (f e2) b
    | StrictEquality (e1, e2) -> Printf.sprintf "(%s %s)" (f e1) (f e2)
    | StrictEqualitySameType (e1, e2) -> Printf.sprintf "(%s %s)" (f e1) (f e2)
 
let rec string_of_statement t =
  match t.stmt_stx with
    | Label l -> Printf.sprintf "label %s" l
    | Goto s -> Printf.sprintf "goto %s" s
    | GuardedGoto (e, s1, s2) -> Printf.sprintf "goto [%s] %s, %s" (string_of_expression e) s1 s2
    | Basic bs -> string_of_basic_statement bs
    | Sugar s -> string_of_sugar s
		| _ -> "illegal_construct()"
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
		| _ -> "illegal_construct()"
			
let rec sexpr_of_statement t tabs i line_numbers_on =
	let str_i = string_of_int i in 
  match t.stmt_stx with
    | Label l -> 
				if (line_numbers_on) 
					then (tabs_to_str tabs) ^ Printf.sprintf "(%s 'label '%s)" str_i l
					else (tabs_to_str tabs) ^ Printf.sprintf "('label '%s)" l
    | Goto s ->  
				if (line_numbers_on) 
					then (tabs_to_str tabs) ^ Printf.sprintf "(%s 'goto '%s)" str_i s
					else (tabs_to_str tabs) ^ Printf.sprintf "('goto '%s)" s
    | GuardedGoto (e, s1, s2) ->  
				if (line_numbers_on) 
					then (tabs_to_str tabs) ^ Printf.sprintf "(%s 'goto %s '%s '%s)" str_i (sexpr_of_expression e) s1 s2
					else (tabs_to_str tabs) ^ Printf.sprintf "('goto %s '%s '%s)" (sexpr_of_expression e) s1 s2
    | SGoto s -> 
			  (* ('goto i) *) 
				if (line_numbers_on)
					then (tabs_to_str tabs) ^ Printf.sprintf "(%s 'goto %s)" str_i (string_of_int s)
					else (tabs_to_str tabs) ^ Printf.sprintf "('goto %s)" (string_of_int s)
    | SGuardedGoto (e, s1, s2) -> 
			  (* ('goto e i j) *) 
			 	if (line_numbers_on)
					then (tabs_to_str tabs) ^  Printf.sprintf "(%s 'goto %s %s %s)" str_i (sexpr_of_expression e) (string_of_int s1) (string_of_int s2)
					else (tabs_to_str tabs) ^  Printf.sprintf "('goto %s %s %s)" (sexpr_of_expression e) (string_of_int s1) (string_of_int s2)
    | Basic bs -> (tabs_to_str tabs) ^ (sexpr_of_basic_statement bs i line_numbers_on)
    | Sugar s -> (sexpr_of_sugar s tabs i line_numbers_on)
(* *)
(* statement list *)
and sexpr_of_statement_list ts tabs line_numbers_on = String.concat "\n" 
 (List.mapi (fun i t -> (sexpr_of_statement t tabs i line_numbers_on)) ts)
(* *)
(* sugar *)
and sexpr_of_sugar t tabs i line_numbers_on =
	let str_i = string_of_int i in
  match t with
    | If (condition, thenbranch, elsebranch) -> 
      (tabs_to_str tabs) ^ 
				(Printf.sprintf "('if %s \n %s \n %s" 
      		(sexpr_of_expression condition)
      		(sexpr_of_statement_list thenbranch (tabs + 1) line_numbers_on)
      		(sexpr_of_statement_list elsebranch (tabs + 1) line_numbers_on)) ^
				(tabs_to_str tabs) ^ ")"
    | SSpecFunction (v, sf, excel_label) ->
				if line_numbers_on  
					then (tabs_to_str tabs) ^ 
									(Printf.sprintf "(%s 'call '%s %s %s ('error %s))" 
     								str_i v (string_of_spec_fun_id sf) (sexpr_of_spec_function sf) (string_of_int excel_label))
					else (tabs_to_str tabs) ^ 
									(Printf.sprintf "('call '%s %s %s ('error %s))" 
     								v (string_of_spec_fun_id sf) (sexpr_of_spec_function sf) (string_of_int excel_label))
		| _ -> "illegal_construct()"
      
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

let remove_labels cmd_list ret_label ex_label = 
	let my_hash = Hashtbl.create 123456 in 
	(* *)
	let label_to_number lab = 
		if (Hashtbl.mem my_hash lab)
			then (Hashtbl.find my_hash lab)
			else -1 in 
	(* *)
	(* register_labels - associate labels with numbers *)
	let rec register_labels cur_cmd_list cur_len = 
		match cur_cmd_list with 
		| [] -> true
		| cmd :: rest_cmd_list ->
			(match cmd.stmt_stx with 
				| Label l ->
						Hashtbl.add my_hash l cur_len;
					 	if ((l != ret_label) && (l != ex_label)) 
					  	then register_labels rest_cmd_list cur_len
							else register_labels rest_cmd_list (cur_len + 1)   		 
				| _ -> register_labels rest_cmd_list (cur_len + 1)) in 
	(* *)
	(* Translate call *)
	let rewrite_call call = 
			(mk_scall 
				call.call_name 
				call.call_scope 
				call.call_this 
				call.call_args 
				(label_to_number call.call_throw_label)) in
	(* *)
	(* replace labels in gotos with respective numbers *)
	let rec remove_labels_iter cur_cmd_list ac_cmd_list = 
		match cur_cmd_list with 
		| [] -> ac_cmd_list
		| cmd :: rest_cmd_list ->
				(match cmd.stmt_stx with 
					| Label l -> 
							if ((l != ret_label) && (l != ex_label))
								then remove_labels_iter rest_cmd_list ac_cmd_list
								else remove_labels_iter rest_cmd_list 
									(ac_cmd_list @ [ (mk_stmt cmd.stmt_data (Basic Skip)) ])
					| Goto l -> remove_labels_iter rest_cmd_list 
							(ac_cmd_list @ [ (mk_stmt cmd.stmt_data (SGoto (label_to_number l))) ])
					| GuardedGoto (expr, l1, l2) -> 
							remove_labels_iter rest_cmd_list 
								(ac_cmd_list @ [ (mk_stmt cmd.stmt_data (SGuardedGoto (expr, (label_to_number l1), (label_to_number l2)))) ])
					| Basic (Assignment ass) -> 
						(match ass.assign_right with 
							| Call call -> 
									let new_cmd = Basic (Assignment (mk_assign ass.assign_left (SCall (rewrite_call call)))) in 
										remove_labels_iter rest_cmd_list 
											(ac_cmd_list @ [ (mk_stmt cmd.stmt_data new_cmd) ])
							| Eval call -> 
									let new_cmd = Basic (Assignment (mk_assign ass.assign_left (SEval (rewrite_call call)))) in 
										remove_labels_iter rest_cmd_list 
											(ac_cmd_list @ [ (mk_stmt cmd.stmt_data new_cmd) ])
							| BuiltinCall call ->  
									let new_cmd = Basic (Assignment (mk_assign ass.assign_left (SBuiltinCall (rewrite_call call)))) in
										remove_labels_iter rest_cmd_list 
											(ac_cmd_list @ [ (mk_stmt cmd.stmt_data new_cmd) ])
							| _ -> remove_labels_iter rest_cmd_list 
											(ac_cmd_list @ [  (mk_stmt cmd.stmt_data (Basic (Assignment ass))) ]))
				 | Basic (Skip) -> remove_labels_iter rest_cmd_list 
														(ac_cmd_list @ [  (mk_stmt cmd.stmt_data (Basic (Skip))) ])
				 | Basic (Mutation mutation) -> remove_labels_iter rest_cmd_list 
														(ac_cmd_list @ [ (mk_stmt cmd.stmt_data (Basic (Mutation mutation))) ])
				 | Sugar (SpecFunction (var, sf, l)) ->
					 		remove_labels_iter rest_cmd_list 
														(ac_cmd_list @ [ (mk_stmt cmd.stmt_data (Sugar (SSpecFunction (var, sf,  (label_to_number l))))) ])
				 | _ -> remove_labels_iter rest_cmd_list ac_cmd_list) in 
	 register_labels cmd_list 0; 
   (remove_labels_iter cmd_list []), (label_to_number ret_label), (label_to_number ex_label)

(** 
	(procedure xpto (arg1 arg2 ...) (body ...) ('return ret_var ret_label) ('error ex_var ex_label))
**)
let sexpr_of_func_block fb line_numbers =
	 let processed_func_body, ret_lab, ex_lab = remove_labels fb.func_body fb.func_ctx.label_return fb.func_ctx.label_throw in
	 let ret_var =  fb.func_ctx.return_var in 
	 let throw_var = fb.func_ctx.throw_var in 
   Printf.sprintf "('procedure '%s \n\t(%s) \n\t('body \n %s \n\t) \n\t('return %s %s) \n\t('throws %s %s) \n )" 
   		fb.func_name 
   		(sexpr_of_formal_params fb.func_params) 
	 		(sexpr_of_statement_list processed_func_body 2 line_numbers)
   		ret_var (string_of_int ret_lab)
   		throw_var (string_of_int ex_lab)

let string_of_all_functions p_exp =
  AllFunctions.fold (fun fid fwc content -> content ^ Printf.sprintf "%s \n" (string_of_func_block fwc)) p_exp ""
  
let string_of_functions p_exp fs =
  let p_exp = AllFunctions.filter (fun fid fwc -> List.mem fid fs) p_exp in
  AllFunctions.fold (fun fid fwc content -> Printf.printf "%s\n" fid; content ^ Printf.sprintf "%s \n" (string_of_func_block fwc)) p_exp ""

(*Printing Offsets for further processing *)

let get_line_numbers func_body =
	let rec get_line_numbers_aux lst cur_line func_body = 
		match func_body with
		| [] -> lst
		| stmt :: rest_func_body -> 
			let offset = stmt.stmt_data.src_offset in 
				match offset with 
				| None -> get_line_numbers_aux lst (cur_line + 1) rest_func_body
				| Some real_offset -> get_line_numbers_aux ((cur_line, real_offset) :: lst) (cur_line + 1) rest_func_body in 
	get_line_numbers_aux [] 0 func_body
	
let rec string_of_line_numbers (line_numbers_list : (int * int) list) : string = 
	match line_numbers_list with 
	| [] -> ""
	| (jsil_offset, js_offset) :: lst -> "(" ^ (string_of_int jsil_offset) ^ "," ^ (string_of_int js_offset) ^ ")\n" ^ (string_of_line_numbers lst)

(* Pulp_Procedure.AllFunctions.iter (fun fid fwc -> create_output fwc (output_folder_name  ^ "/" ^ functions_folder_name)) p_exp; *)

let create_output_line_numbers (fb : Pulp_Procedure.function_block) file_name ac = 
	let line_number_list = get_line_numbers fb.func_body in 
	let line_number_list_str = string_of_line_numbers line_number_list in 
	let content = "Proc: " ^ fb.func_name ^ "\n" ^ line_number_list_str in 
  	ac ^ content

let get_all_line_numbers procs file_name =
	let content = Pulp_Procedure.AllFunctions.fold 
		(fun fid fwc ac -> create_output_line_numbers fwc file_name ac)	procs	"" in 
	let oc = open_out file_name in 
		output_string oc content;
		close_out oc
		
let generate_offset_lst str =
	let rec traverse_str ac_offset cur_str offset_lst =
		let new_line_index = 
			(try String.index cur_str '\n' with 
				| _ -> -1) in 
			if new_line_index == -1 then
				offset_lst 
			else
				let len = String.length cur_str in 
				let new_str = (try 
						String.sub cur_str (new_line_index + 1) ((len - new_line_index) - 1) with 
						| _ ->
							(* print_string ("bananas: " ^ (string_of_int new_line_index) ^ "\n"); *)
							"") in
						(* print_string ("new_line_index: " ^  (string_of_int new_line_index) ^ "; new_str: " ^ new_str ^ "; len: " ^ (string_of_int len) ^ "\n"); *)
						traverse_str (ac_offset + new_line_index + 1) new_str (offset_lst @ [ (ac_offset + new_line_index + 1) ]) in 
		traverse_str 0 str [] 

let jsoffsetchar_to_jsoffsetline charoffset offset_list =
	let rec offsetchar_to_offsetline_aux c_offset offset_list cur_line =
		match offset_list with 
		| [] -> 1
		| hd :: rest -> 
			if c_offset < hd 
				then 
					cur_line 
				else
					offsetchar_to_offsetline_aux c_offset rest (cur_line + 1) in 
		offsetchar_to_offsetline_aux charoffset offset_list 1

let jsoffsetchar_to_jsoffsetline_str charoffset str =
	let offset_list = generate_offset_lst str in  
	let rec offsetchar_to_offsetline_aux c_offset offset_list cur_line =
		match offset_list with 
		| [] -> 1
		| hd :: rest -> 
			if c_offset < hd 
				then 
					cur_line 
				else
					offsetchar_to_offsetline_aux c_offset rest (cur_line + 1) in 
		offsetchar_to_offsetline_aux charoffset offset_list 1
	 
let memoized_offsetchar_to_offsetline str = 
	let offset_list = generate_offset_lst str in 
	let ht = Hashtbl.create (String.length str) in 
	  fun c_offset -> 
			try Hashtbl.find ht c_offset 
			with Not_found ->
				begin  
				let l_offset =  jsoffsetchar_to_jsoffsetline c_offset offset_list in 
					Hashtbl.add ht c_offset l_offset; 
					l_offset
				end
	


