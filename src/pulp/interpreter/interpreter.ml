(* ./src/pulp/interpreter/interpreter.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open Batteries
open Pulp_Syntax 
open Pulp_Syntax_Utils
open Pulp_Syntax_Print
open Pulp_Procedure
open Memory_Model
open Interpreter_Print

exception InterpreterNotImplemented of string
exception InterpreterStuck of string * int

module LabelMap = Map.Make ( 
  struct 
    type t = label
    let compare = compare
  end
)

let heap_value_arith op v1 v2 counter =
  match v1, v2 with
    |  HVLiteral (Num n1),  HVLiteral (Num n2) -> 
      begin match op with
        | Plus -> HVLiteral (Num (n1 +. n2))
        | Minus -> HVLiteral (Num (n1 -. n2))
        | Times -> HVLiteral (Num (n1 *. n2))
        | Div -> HVLiteral (Num (n1 /. n2))
        | Mod -> HVLiteral (Num (mod_float n1 n2))
      end
    | HVLiteral (String s1),  HVLiteral (String s2) -> HVLiteral (String (s1 ^ s2))
    | _, _ -> raise (InterpreterStuck ("Arith Op on non-numbers", counter))

let value_arith op v1 v2 counter = 
  match v1, v2 with
    | (VHValue hv1), (VHValue hv2) -> VHValue (heap_value_arith op hv1 hv2 counter)
    | _, _ -> raise (InterpreterStuck ("Arith Op on non-numbers", counter))

let heap_value_bool op v1 v2 counter =
  match v1, v2 with
     | HVLiteral (Bool b1), HVLiteral (Bool b2) -> 
      begin match op with
        | And -> HVLiteral (Bool (b1 && b2))
        | Or -> HVLiteral (Bool (b1 || b2))
      end
    | _, _ -> 
      raise (InterpreterStuck ("Boolean Op on non-boolean values\n", counter))

let value_bool op v1 v2 counter =
  match v1, v2 with
    | (VHValue hv1), (VHValue hv2) -> VHValue (heap_value_bool op hv1 hv2 counter)
    | _, _ -> 
      raise (InterpreterStuck ("Boolean Op on non-boolean values", counter))
      
let heap_value_less_than v1 v2 counter =
  match v1, v2 with
    | HVLiteral (Num n1), HVLiteral (Num n2) -> compare n1 n2 < 0
    | HVLiteral (String s1), HVLiteral (String s2) -> compare s1 s2 < 0
    | _,_ -> raise (InterpreterStuck ("< on non-number values", counter))

let value_less_than v1 v2 counter =
  match v1, v2 with
    | VHValue hv1, VHValue hv2 -> heap_value_less_than hv1 hv2 counter
    (*| VRef (l1, s1, rt1), VRef (l2, s2, rt2) -> false*)
    | _, _ -> raise (InterpreterStuck ("< on non-number values", counter))

(* Taken from jscert *)
let to_int32 = fun n ->
  match classify_float n with
  | FP_normal | FP_subnormal ->
    let i32 = 2. ** 32. in
    let i31 = 2. ** 31. in
    let posint = (if n < 0. then (-1.) else 1.) *. (floor (abs_float n)) in
    let int32bit =
      let smod = mod_float posint i32 in
      if smod < 0. then smod +. i32 else smod
    in
    (if int32bit >= i31 then int32bit -. i32 else int32bit)
  | _ -> 0.

let to_uint32 = fun n ->
  match classify_float n with
  | FP_normal | FP_subnormal ->
    let i32 = 2. ** 32. in
    let posint = (if n < 0. then (-1.) else 1.) *. (floor (abs_float n)) in
    let int32bit =
      let smod = mod_float posint i32 in
      if smod < 0. then smod +. i32 else smod
    in
    int32bit
  | _ -> 0.

let modulo_32 = (fun x -> let r = mod_float x 32. in if x < 0. then r +. 32. else r)

let int32_bitwise_not = fun x -> Int32.to_float (Int32.lognot (Int32.of_float x))

let int32_bitwise_and = fun x y -> Int32.to_float (Int32.logand (Int32.of_float x) (Int32.of_float y))

let int32_bitwise_or = fun x y -> Int32.to_float (Int32.logor (Int32.of_float x) (Int32.of_float y))

let int32_bitwise_xor = fun x y -> Int32.to_float (Int32.logxor (Int32.of_float x) (Int32.of_float y))

let int32_left_shift x y =
  let l = Int32.of_float x in
  let r = (int_of_float y) mod 32 in
  Int32.to_float (Int32.shift_left l r)

let int32_right_shift x y =
  let l = Int32.of_float x in
  let r = (int_of_float y) mod 32 in
  Int32.to_float (Int32.shift_right l r)

let uint32_right_shift = (fun x y ->
  let i31 = 2. ** 31. in
  let i32 = 2. ** 32. in
  let signedx = if x >= i31 then x -. i32 else x in
  let left = Int32.of_float signedx in
  let right = (int_of_float y) mod 32 in
  let r = Int32.to_float (Int32.shift_right_logical left right) in
  if r < 0. then r +. i32 else r)

let run_bin_op op v1 v2 counter : value =
  begin match op with
    | Concat ->
      begin match v1, v2 with
        | VHValue (HVLiteral (String s1)),  VHValue (HVLiteral (String s2)) -> VHValue (HVLiteral (String (s1 ^ s2)))
        | _ -> raise (InterpreterStuck ("Concatenation non-string values", counter))
      end
    | Comparison cop ->
      begin match cop with
        | Equal -> VHValue (HVLiteral (Bool (value_eq v1 v2)))
        | LessThan -> VHValue (HVLiteral (Bool (value_less_than v1 v2 counter)))
        | LessThanEqual -> raise (InterpreterStuck ("Not Implemented <=", counter))
      end
    | Subtype -> 
      begin match v1, v2 with
        | VType t1, VType t2 -> VHValue (HVLiteral (Bool (Type_Info.is_subtype t1 t2)))
        | v1, v2 -> raise (InterpreterStuck ("Subtype on non type literals " ^ (Interpreter_Print.string_of_value v1) ^ " " ^ (Interpreter_Print.string_of_value v2), counter))
      end
    | Arith aop -> value_arith aop v1 v2 counter
    | Boolean bop -> value_bool bop v1 v2 counter
    | Bitwise bop ->
      let n1, n2 = match v1, v2 with
        | VHValue (HVLiteral (Num n1)),  VHValue (HVLiteral (Num n2)) -> n1, n2 
        | _ -> raise (InterpreterStuck ("Bitwise on non-number values", counter)) in
      VHValue (HVLiteral (Num ( 
        begin match bop with
          | BitwiseAnd -> int32_bitwise_and n1 n2
          | BitwiseOr -> int32_bitwise_or n1 n2
          | BitwiseXor -> int32_bitwise_xor n1 n2
          | LeftShift -> int32_left_shift n1 n2
          | SignedRightShift -> int32_right_shift n1 n2
          | UnsignedRightShift -> uint32_right_shift n1 n2
        end)))
  end
  
let bool_not v counter =
  match v with
    | VHValue HVLiteral (Bool b) -> VHValue (HVLiteral (Bool (not b)))
    | _ -> raise (InterpreterStuck ("Cannot proceed with not on reference/type value", counter))

let num_negative v counter =
  match v with
    | VHValue (HVLiteral (Num n)) -> VHValue (HVLiteral (Num (-.n))) 
    | _ -> raise (InterpreterStuck ("Cannot proceed with negative on not number value", counter))

let num_to_string v counter =
  match v with
    | VHValue (HVLiteral (Num n)) -> VHValue (HVLiteral (String (Utils.float_to_string_inner n))) 
    | _ -> raise (InterpreterStuck ("Cannot proceed with num_to_string on not number value", counter))

let string_to_num v counter =
  match v with
    | VHValue (HVLiteral (String s)) -> begin
      match String.trim s with
        | "" -> VHValue (HVLiteral (Num 0.))
        | _ ->
        begin 
          let num = 
            try
              Float.of_string s 
            with Failure "float_of_string" -> nan in
          VHValue (HVLiteral (Num num)) 
        end
      end
    | _ -> raise (InterpreterStuck ("Cannot proceed with string_to_num on not string value", counter))

let num_to_int32 v counter =
  match v with
    | VHValue (HVLiteral (Num n)) -> VHValue (HVLiteral (Num (to_int32 n))) 
    | _ -> raise (InterpreterStuck ("Cannot proceed with num_to_int32 on not number value", counter))

let num_to_uint32 v counter =
  match v with
    | VHValue (HVLiteral (Num n)) -> VHValue (HVLiteral (Num (to_uint32 n))) 
    | _ -> raise (InterpreterStuck ("Cannot proceed with num_to_uint32 on not number value", counter))

let bitwise_not v counter =
  match v with
    | VHValue (HVLiteral (Num n)) -> VHValue (HVLiteral (Num (int32_bitwise_not n))) 
    | _ -> raise (InterpreterStuck ("Cannot proceed with ! on not number value", counter))
  
let run_unary_op op v counter : value =
  match op with
    | Not -> bool_not v counter 
    | Negative -> num_negative v counter
    | ToStringOp -> num_to_string v counter
    | ToNumberOp -> string_to_num v counter
    | ToInt32Op ->  num_to_int32 v counter
    | ToUint32Op ->  num_to_uint32 v counter
    | BitwiseNot -> bitwise_not v counter
 
let type_of_literal l =
  match Type_Info.get_pulp_type (Type_Info.get_type_info_literal(l)) with
    | None -> raise (InterpreterStuck ("Empty does not have a type", 0))
    | Some pt -> pt

let type_of v =
  match v with
    | VHValue hv ->
      begin match hv with
        | HVLiteral lit -> type_of_literal lit
        | HVObj (BLoc _) -> ObjectType (Some Builtin)
        | HVObj (Loc _) -> ObjectType (Some Normal)
      end
    | VRef (_, _, rt) -> ReferenceType (Some rt)
    | VType _ -> StringType (* Shouldn't be called at all? *)

let object_check v error counter = 
  match v with
    | VHValue (HVLiteral (LLoc l)) -> BLoc l
    | VHValue (HVObj l) -> l
    | _ -> raise (InterpreterStuck (error, counter))

let string_check v error counter = 
  match v with
    | VHValue (HVLiteral (String x)) -> x
    | _ -> raise (InterpreterStuck (error, counter))

let field_check v error counter = 
  match v with
    | VHValue (HVLiteral (String x)) -> (UserField x)
    | VHValue (HVLiteral (BField f)) -> (BuiltinField f)
    | _ -> raise (InterpreterStuck (error, counter))

let object_field_check v1 v2 h cmd_name counter = 
	  let l = object_check v1 ("First argument of " ^ cmd_name ^ " must be an object") counter in
	  let x = field_check v2 ("Second argument of " ^ cmd_name ^ " must be a field") counter in
    try
      (l, x, Heap.find l h)
    with
      | Not_found -> raise (InterpreterStuck ("Object must exists for " ^ cmd_name, counter))

    
type local_state = {
  lsheap : heap_type;
  lsstack : stack_type;
  lscounter : int;
  lsexcep : label option;
}

type function_return_type =
  | FTException
  | FTReturn      
      
type function_state = {
    fs_heap : heap_type;
    fs_return_type : function_return_type;
    fs_return_value : value 
} 

let end_label stmt labelmap ctx =
  match stmt.stmt_stx with
    | Label l -> l = ctx.label_return || l = ctx.label_throw
    | _ -> false
  
let rec run_expr (s : local_state) (e : expression) : value =
  match e with
	  | Literal l ->
      begin match l with
        | LLoc bl -> VHValue (HVObj (BLoc bl))
        | Type t -> VType t
        | _ -> VHValue (HVLiteral l)
      end
	  | Var v -> 
      (try 
        Stack.find v s.lsstack
      with Not_found -> raise (InterpreterStuck ("Cannot find a variable" ^ v ^ "in the stack", s.lscounter)))
	  | BinOp (e1, op, e2) -> 
      let v1 = run_expr s e1 in
      let v2 = run_expr s e2 in
      run_bin_op op v1 v2 s.lscounter
	  | UnaryOp (op, e) -> 
      let v1 = run_expr s e in
      run_unary_op op v1 s.lscounter
	  | Ref (e1, e2, rt) -> 
      let v = run_expr s e1 in
      let x = run_expr s e2 in
      let hv = match v with
        | VHValue hv -> hv
        | VType _ -> raise (InterpreterStuck ("First parameter of reference cannot be a type", s.lscounter))
        | VRef _ -> raise (InterpreterStuck ("First parameter of reference cannot be a reference", s.lscounter)) in
      let xfield = field_check x "Second element of reference should be string" s.lscounter in
      VRef (hv, xfield, rt)
	  | Base e -> 
      let v = run_expr s e in
      begin match v with
        | VRef (v, x, rt) -> VHValue v
        | _ -> raise (InterpreterStuck ("Base is only defined on references", s.lscounter))
      end
	  | Field e ->       
      let v = run_expr s e in
      begin match v with
        | VRef (l, x, rt) ->
          begin match x with
            | BuiltinField x ->  VHValue (HVLiteral (BField x))
            | UserField x -> VHValue (HVLiteral (String x))
          end
        | _ -> raise (InterpreterStuck ("Field is only defined on references", s.lscounter))
      end
    | TypeOf (e) ->
      let v = run_expr s e in
      let t = type_of v in
      (*Printf.printf "TypeOf (%s) = %s \n" (Interpreter_Print.string_of_value v) (Pulp_Syntax_Print.string_of_pulp_type t);*)
      VType t
      
      
let rec get_value_proto v x h counter =
  match v with
    (* Should it be undefined descriptor? *)
    | VHValue (HVLiteral Null) -> VHValue (HVLiteral Empty)
    | _ ->
      let l = object_check v "First argument of Proto must be an object" counter in
		  let obj = 
        try Heap.find l h 
        with | Not_found -> raise (InterpreterStuck ("Object must exists for Proto", counter)) in
	    try
	      let v = Object.find x obj in VHValue v
	    with | Not_found -> 
		    try 
		      let proto = Object.find (BuiltinField FProto) obj in
		      get_value_proto (VHValue proto) x h counter
		    with
		      | Not_found -> raise (InterpreterStuck ("Object must have prototype in Proto", counter))

let rec is_proto_obj l o h counter =
  (*Printf.printf "Running is_proto %s %s \n" (Interpreter_Print.string_of_value l) (Interpreter_Print.string_of_loc o);*)
  match l with
    (* Should it be undefined descriptor? *)
    | VHValue (HVLiteral Null) -> VHValue (HVLiteral (Bool false))
    | _ ->
      let ll = object_check l "First argument of proto_obj must be an object" counter in     
      if (ll = o)  then VHValue (HVLiteral (Bool true))     
		  else begin	  
			  let obj = 
			    try Heap.find ll h 
			    with 
			      | Not_found -> raise (InterpreterStuck ("Object must exists for proto_obj", counter)) in
			    try 
			      let proto = Object.find (BuiltinField FProto) obj in
			      is_proto_obj (VHValue proto) o h counter
			    with
			      | Not_found -> raise (InterpreterStuck ("Object must have prototype in proto_obj", counter))
			end 
      
(* TODO -- I don't like the code here *)
let rec run_assign_expr (s : local_state) (e : assign_right_expression) ctx (funcs : function_block AllFunctions.t) (env : function_block AllFunctions.t) : local_state * value =
  let run_call c builtin =
      let fid = run_expr s c.call_name in
      let fid_string = string_check fid "Function name should be a string" s.lscounter in
      let fblock = 
        try AllFunctions.find fid_string funcs 
        with | Not_found -> 
          begin 
            try AllFunctions.find fid_string env with
              | Not_found -> raise (InterpreterStuck ("Cannot find the function by name" ^ fid_string, s.lscounter))
          end
      in  
      let vthis = run_expr s c.call_this in
      let vscope = run_expr s c.call_scope in
      let vargs = List.map (run_expr s) c.call_args in
      let fs = run_function s.lsheap fblock ([vthis; vscope] @ vargs) funcs env builtin in
      begin match fs.fs_return_type with
        | FTException -> {s with lsheap = fs.fs_heap; lsexcep = Some (c.call_throw_label)}, fs.fs_return_value
        | FTReturn -> {s with lsheap = fs.fs_heap}, fs.fs_return_value
      end in
	(* Assignment expressions *)
  match e with
    | Expression ae -> s, run_expr s ae
    | BuiltinCall c -> run_call c true
	  | Call c -> run_call c false
    | Eval c -> 
      let vthis = run_expr s c.call_this in
      let vscope = run_expr s c.call_scope in
      let arg = match c.call_args with
        | [] -> raise (InterpreterStuck ("Eval should have one argument", s.lscounter))
        | arg :: tail -> arg in
      let varg = run_expr s arg in
      let varg = match varg with
        | VHValue (HVLiteral (String s)) -> s
        | _ -> raise (InterpreterStuck ("Eval argument must be string", s.lscounter)) in
             
     begin try       
	     let exp = Parser_main.exp_from_string varg in  
	    
	     (* TODO update all_functions *)
	     let eval_main = fresh_named "eval" in
	    
	     (*Printf.printf "Env vars in Eval: %s" (String.concat "\n" (List.map (Pulp_Syntax_Print.string_of_ctx_vars) ctx.env_vars));*)
	     let pexp, penv = Pulp_Translate.exp_to_pulp Pulp_Translate.IVL_goto_unfold_functions exp eval_main ctx.env_vars in
	    
	     let funcs = AllFunctions.fold (fun key value result -> AllFunctions.add key value result) pexp funcs in
	      
	     let main = AllFunctions.find eval_main pexp in  
	   
	      let fs = run_function s.lsheap main ([vthis; vscope]) funcs env true in
	      begin match fs.fs_return_type with
	        | FTException -> {s with lsheap = fs.fs_heap; lsexcep = Some (c.call_throw_label)}, fs.fs_return_value
	        | FTReturn -> {s with lsheap = fs.fs_heap}, fs.fs_return_value
	      end
     
      with | Parser.ParserFailure _ | Pulp_Translate.PulpEarlySyntaxError _ ->
        begin
          let l = Loc (fresh_loc ()) in
          let newobj = Object.add (BuiltinField FClass) (HVLiteral (String "Error")) Object.empty in
          let newobj = Object.add (BuiltinField FProto) (HVObj (BLoc Lsep)) newobj in
          {s with lsheap = Heap.add l newobj s.lsheap; lsexcep = Some (c.call_throw_label)}, VHValue (HVObj l)
        end
      end
      
	  | Obj -> 
      let l = Loc (fresh_loc ()) in
      {s with lsheap = Heap.add l  Object.empty s.lsheap}, VHValue (HVObj l)
	  | HasField (e1, e2) -> 
      let v1 = run_expr s e1 in
      let v2 = run_expr s e2 in 
      let l, x, obj = object_field_check v1 v2 s.lsheap "HasField" s.lscounter in
      let rv = 
        try let _ = Object.find x obj in true
        with | Not_found -> false in
      s, VHValue (HVLiteral (Bool rv))
	  | Lookup (e1, e2) -> 
      let v1 = run_expr s e1 in
      let v2 = run_expr s e2 in
			let l, x, obj = object_field_check v1 v2 s.lsheap "Lookup" s.lscounter in
      let v = 
        try Object.find x obj 
			  with | Not_found -> raise (InterpreterStuck ("Couldn't proceed with Lookup", s.lscounter)) in
      s, (VHValue v)
	  | Deallocation (e1, e2) -> 
      let v1 = run_expr s e1 in
      let v2 = run_expr s e2 in
			let l, x, obj = object_field_check v1 v2 s.lsheap "Deallocation" s.lscounter in
	    let _ = 
        try Object.find x obj 
        with | Not_found -> raise (InterpreterStuck ("Couldn't proceed with Deallocation", s.lscounter)) in
	    let newobj = Object.remove x obj in
	    {s with lsheap = Heap.add l newobj s.lsheap}, VHValue (HVLiteral (Bool true))

	  | ProtoF (e1, e2) -> 
      let v1 = run_expr s e1 in
      let v2 = run_expr s e2 in	
      (*Printf.printf ("proto_field (%s, %s)") (string_of_value v1) (string_of_value v2);*)
			let l, x, obj = object_field_check v1 v2 s.lsheap "proto_field" s.lscounter in
			let v = get_value_proto (VHValue (HVObj l)) x s.lsheap s.lscounter in s, v 
      
   | ProtoO (e1, e2) -> 
      let v1 = run_expr s e1 in
      let v2 = run_expr s e2 in 
      let l1 = object_check v1 "proto_obj" s.lscounter in
      let l2 = object_check v2 "proto_obj" s.lscounter in
      let v = is_proto_obj (VHValue (HVObj l1)) l2 s.lsheap s.lscounter in s, v 
and
run_function (h : heap_type) (f : function_block) (args : value list) (fs : function_block AllFunctions.t) (env : function_block AllFunctions.t) (is_builtin) : function_state =
  (* I cannot do the following syntactically, can I? *)
  (*Printf.printf "Running function %s \n" f.func_name;*)
  let args_mod = List.mapi (fun index param -> 
    if List.length args > index then List.nth args index
    else (if is_builtin then (VHValue (HVLiteral Empty)) else (VHValue (HVLiteral Undefined)))
  ) f.func_params in
  
  let s = List.fold_left2 (fun st param arg -> Stack.add param arg st) Stack.empty f.func_params args_mod in
  
  let s = Stack.add f.func_ctx.return_var (VHValue (HVLiteral Empty)) s in
  let s = Stack.add f.func_ctx.throw_var (VHValue (HVLiteral Empty)) s in
    
  let _, label_index = List.fold_left (fun (index, li) stmt ->
    match stmt.stmt_stx with
      | Label l -> (index + 1, LabelMap.add l index li)
      | _ -> index + 1, li
    ) (0, LabelMap.empty) f.func_body in
    
  let result = run_stmts f.func_body f.func_ctx {lsheap = h; lsstack = s; lscounter = 0; lsexcep = None} label_index fs env in
  (*Printf.printf "End of function %s \n" f.func_name;*)
  let ret_type, ret_val = 
    let stmt = List.nth f.func_body result.lscounter in
    let l = match stmt.stmt_stx with
      | Label l -> l
      | _ -> raise (Invalid_argument "Shouldn't be other stametemnt than Label statemment here") in
    if l = f.func_ctx.label_return then FTReturn, 
       (try Stack.find f.func_ctx.return_var result.lsstack 
        with Not_found -> raise (InterpreterStuck ("Cannot find return variable", result.lscounter)))
    else if l = f.func_ctx.label_throw then FTException, 
       (try Stack.find f.func_ctx.throw_var result.lsstack
        with Not_found -> raise (InterpreterStuck ("Cannot find throw variable", result.lscounter)))
    else raise (Invalid_argument "Shouldn't be other label than end label here");    
  in 
  (*Printf.printf "End of function %s \n" f.func_name;*)
  {fs_heap = result.lsheap; fs_return_type = ret_type; fs_return_value = ret_val}
  
and run_basic_stmt (s : local_state) (stmt : basic_statement) (labelmap : int LabelMap.t) ctx (fs : function_block AllFunctions.t) (env : function_block AllFunctions.t) : local_state =
   match stmt with
    | Skip -> {s with lscounter = s.lscounter + 1}
    | Assignment assign -> 
      let s, v = run_assign_expr s assign.assign_right ctx fs env in
      (*Printf.printf ("Assigning %s := %s") assign.assign_left (Interpreter_Print.string_of_value v);*)
      begin match s.lsexcep with
        | Some throwl ->
          let counter = try LabelMap.find throwl labelmap with Not_found -> raise (InterpreterStuck ("Cannot find throw label " ^ throwl, s.lscounter)) in  
        {s with 
          lsstack = Stack.add assign.assign_left v s.lsstack; 
          lscounter = counter;
          lsexcep = None
        }
        | None -> {s with lsstack = Stack.add assign.assign_left v s.lsstack; lscounter = s.lscounter + 1}
      end
    | Mutation m -> 
      let v1 = run_expr s m.m_loc in
      let v2 = run_expr s m.m_field in
      let v3 = run_expr s m.m_right in
            let l, x, obj = object_field_check v1 v2 s.lsheap "Mutation" s.lscounter in
            let v3 = match v3 with
              | VHValue v -> v
              | VType _ -> raise (InterpreterStuck ("Right hand side of mutation cannot be a type", s.lscounter))
              | VRef _ -> raise (InterpreterStuck ("Right hand side of mutation cannot be a reference", s.lscounter)) in
            let newobj = Object.add x v3 obj in
            {s with lsheap = Heap.add l newobj s.lsheap; lscounter = s.lscounter + 1}

and run_stmt (s : local_state) (stmt : statement) (labelmap : int LabelMap.t) (ctx) (fs : function_block AllFunctions.t) (env : function_block AllFunctions.t) : local_state =
  (*Printf.printf "Running stmt %s \n" (Pulp_Syntax_Print.string_of_statement stmt);*)
  match stmt.stmt_stx with
    | Label l -> {s with lscounter = s.lscounter + 1}
    | Goto l -> let counter = try LabelMap.find l labelmap with Not_found -> raise (InterpreterStuck ("Cannot find label in Goto " ^ l, s.lscounter)) in
      {s with lscounter = counter}
    | GuardedGoto (e, l1, l2) -> 
      let v = run_expr s e in
      begin match v with
        | VHValue (HVLiteral (Bool true)) ->
          let counter = try LabelMap.find l1 labelmap with Not_found -> raise (InterpreterStuck ("Cannot find label in Goto " ^ l1, s.lscounter)) in
          {s with lscounter = counter}
        | VHValue (HVLiteral (Bool false)) ->
          let counter = try LabelMap.find l2 labelmap with Not_found -> raise (InterpreterStuck ("Cannot find label in Goto " ^ l2, s.lscounter)) in
          {s with lscounter = counter}
        | _ -> raise (InterpreterStuck ("GuardedGoto expression must evaluate to boolean value", s.lscounter))
      end
    | Basic bs -> run_basic_stmt s bs labelmap ctx fs env
    | Sugar sss -> raise (InterpreterNotImplemented ("Syntactic Sugar" ^ (Pulp_Syntax_Print.string_of_sugar sss)))

and run_stmts stmts ctx lstate labelmap fs env =
  let next_stmt = List.nth stmts lstate.lscounter in
  if end_label next_stmt labelmap ctx then lstate 
  else 
    let state = run_stmt lstate next_stmt labelmap ctx fs env in
    run_stmts stmts ctx state labelmap fs env
    
let run (h: heap_type) main_this main_scope (fs : function_block AllFunctions.t) (env : function_block AllFunctions.t) : function_state = 
  let main = AllFunctions.find main_fun_id fs in
  run_function h main [main_this; main_scope] fs env false
  
let built_in_obj_proto_lop h obj =
  let l = Object.add (BuiltinField FProto) (HVObj (BLoc Lop)) Object.empty in
  Heap.add (BLoc obj) l h
  
let built_in_obj_proto_lfp h obj =
  let l = Object.add (BuiltinField FProto) (HVObj (BLoc Lfp)) Object.empty in
  Heap.add (BLoc obj) l h
  
let add_field h l f v =
  let obj = try Heap.find l h with Not_found -> raise (InterpreterStuck ("Cannot find object " ^ (Interpreter_Print.string_of_loc l), -1)) in
  let obj = Object.add f v obj in
  Heap.add l obj h

let add_builtin_function h loc id len =
  let h = built_in_obj_proto_lfp h loc in
  let h = add_field h (BLoc loc) (BuiltinField FId) (HVLiteral (String (string_of_builtin_function id))) in
  let h = add_field h (BLoc loc) (BuiltinField FClass) (HVLiteral (String "Function")) in
  let h = add_field h (BLoc loc) (UserField "length") (HVLiteral (Num len)) in
  h

let native_error h name loc locp builtin =
  let h = built_in_obj_proto_lfp h loc in
  let h = add_field h (BLoc Lg) (UserField name) (HVObj (BLoc loc)) in
  let h = add_field h (BLoc loc) (BuiltinField FClass) (HVLiteral (String "Function")) in
  (* FIXME constructor/caller names *)
  let h = add_field h (BLoc loc) (BuiltinField FId) (HVLiteral (String (string_of_builtin_function builtin))) in
  let h = add_field h (BLoc loc) (BuiltinField FConstructId) (HVLiteral (String (string_of_builtin_function builtin))) in
  let h = add_field h (BLoc loc) (UserField "length") (HVLiteral (Num 1.)) in
  let h = add_field h (BLoc loc) (UserField "prototype") (HVObj (BLoc locp)) in

  let proto = Object.add (BuiltinField FProto) (HVObj (BLoc Lep)) Object.empty in
  let h = Heap.add (BLoc locp) proto h in
  let h = add_field h (BLoc locp) (BuiltinField FClass) (HVLiteral (String "Error")) in
  let h = add_field h (BLoc locp) (UserField "constructor") (HVObj (BLoc loc)) in
  let h = add_field h (BLoc locp) (UserField "name") (HVLiteral (String name)) in
  let h = add_field h (BLoc locp) (UserField "message") (HVLiteral (String "")) in
  h

let add_stub_function h parent field =
  let name = (match parent with
    | (LStub pname) -> pname ^ "." ^ field
    | _ -> field
  ) in
  let loc = LStub name in
  let h = add_builtin_function h loc (Not_Implemented_Stub name) 1. in
  let h = add_field h (BLoc parent) (UserField field) (HVObj (BLoc loc)) in
  h

let fold_add_stub_function h parent = List.fold_left ((flip add_stub_function) parent) h

let add_stub_callable h name len =
  (* Callable *)
  let loc = BLoc (LStub name) in
  let h = built_in_obj_proto_lfp h (LStub name) in
  let h = add_field h (BLoc Lg) (UserField name) (HVObj loc) in
  let h = add_field h loc (BuiltinField FId) (HVLiteral (String (string_of_builtin_function (Not_Implemented_Stub (name ^ "#call"))))) in
  let h = add_field h loc (BuiltinField FClass) (HVLiteral (String "Function")) in
  let h = add_field h loc (UserField "length") (HVLiteral (Num len)) in
  (* Callable Prototype *)
  let namep = name ^ "P" in
  let locp = BLoc (LStub namep) in
  let h = built_in_obj_proto_lop h (LStub namep) in
  let h = add_field h loc (UserField "prototype") (HVObj locp) in
  let h = add_field h locp (BuiltinField FClass) (HVLiteral (String name)) in
  let h = add_field h locp (UserField "constructor") (HVObj loc) in
  h

let add_stub_constructor h name len =
  let h = add_stub_callable h name len in
  (* Constructor *)
  let loc = BLoc (LStub name) in
  let h = add_field h loc (BuiltinField FConstructId) (HVLiteral (String (string_of_builtin_function (Not_Implemented_Stub (name ^ "#construct"))))) in
  h

(* TODO refactor to use functions as in stubs *)
let initial_heap () =
  let h = Heap.empty in
  let lop = Object.add (BuiltinField FProto) (HVLiteral Null) Object.empty in
  let h = Heap.add (BLoc Lop) lop h in
  let h = List.fold_left built_in_obj_proto_lop h [Lg; Lfp; LMath; LJSON;
    LNotImplemented GetValuePrim; LNotImplemented ToNumber; LNotImplemented ToString; Lbp; Lnp; Lsp; Lep; Lap] in
  let h = List.fold_left built_in_obj_proto_lfp h [LObject; LFunction; LBoolean; LNumber; LString; LError; LArray] in
    
  let h = add_field h (BLoc Lop) (BuiltinField FClass) (HVLiteral (String "Object")) in
  let h = add_builtin_function h Lop_toString Object_Prototype_toString 0. in
  let h = add_field h (BLoc Lop) (UserField "toString") (HVObj (BLoc Lop_toString)) in
  let h = add_builtin_function h Lop_valueOf Object_Prototype_valueOf 0. in
  let h = add_field h (BLoc Lop) (UserField "valueOf") (HVObj (BLoc Lop_valueOf)) in
  let h = add_builtin_function h Lop_isPrototypeOf Object_Prototype_isPrototypeOf 1. in
  let h = add_field h (BLoc Lop) (UserField "isPrototypeOf") (HVObj (BLoc Lop_isPrototypeOf)) in
  let h = add_field h (BLoc Lop) (UserField "constructor") (HVObj (BLoc LObject)) in
  let h = add_stub_function h Lop "toLocaleString" in
  let h = add_stub_function h Lop "hasOwnProperty" in
  let h = add_stub_function h Lop "propertyIsEnumerable" in
    
  let h = add_field h (BLoc Lg) (BuiltinField FClass) (HVLiteral (String "Global Object")) in
  let h = add_field h (BLoc Lg) (UserField "undefined") (HVLiteral Undefined) in
  let h = add_field h (BLoc Lg) (UserField "NaN") (HVLiteral (Num nan)) in
  let h = add_field h (BLoc Lg) (UserField "Infinity") (HVLiteral (Num infinity)) in
  let h = add_builtin_function h LEval Global_eval 1. in
  let h = add_field h (BLoc Lg) (UserField "eval") (HVObj (BLoc LEval)) in
  let h = add_builtin_function h Lg_isNaN Global_isNaN 1. in
  let h = add_field h (BLoc Lg) (UserField "isNaN") (HVObj (BLoc Lg_isNaN)) in
  let h = add_builtin_function h Lg_isFinite Global_isFinite 1. in
  let h = add_field h (BLoc Lg) (UserField "isFinite") (HVObj (BLoc Lg_isFinite)) in
  let h = fold_add_stub_function h Lg
    ["parseInt"; "parseFloat"; "decodeURI"; "decodeURIComponent"; "encodeURI"; "encodeURIComponent"] in
  
  let h = add_field h (BLoc Lg) (UserField "Object") (HVObj (BLoc LObject)) in
  let h = add_field h (BLoc LObject) (BuiltinField FClass) (HVLiteral (String "Function")) in
  let h = add_field h (BLoc LObject) (BuiltinField FId) (HVLiteral (String (string_of_builtin_function Object_Call))) in
  let h = add_field h (BLoc LObject) (BuiltinField FConstructId) (HVLiteral (String (string_of_builtin_function Object_Construct))) in
  let h = add_field h (BLoc LObject) (UserField "prototype") (HVObj (BLoc Lop)) in
  let h = add_field h (BLoc LObject) (UserField "length") (HVLiteral (Num 1.)) in
  let h = add_builtin_function h LObjectGetPrototypeOf Object_getPrototypeOf 1. in
  let h = add_field h (BLoc LObject) (UserField "getPrototypeOf") (HVObj (BLoc LObjectGetPrototypeOf)) in
  let h = fold_add_stub_function h LObject
    ["getOwnPropertyDescriptor"; "getOwnPropertyNames"; "create"; "defineProperty"; "defineProperties"; "seal"; "freeze";
    "preventExtensions"; "isSealed"; "isFrozen"; "isExtensible"; "keys"] in
  
  let h = add_field h (BLoc Lg) (UserField "Function") (HVObj (BLoc LFunction)) in
  let h = add_field h (BLoc LFunction) (BuiltinField FId) (HVLiteral (String (string_of_builtin_function Function_Call))) in
  let h = add_field h (BLoc LFunction) (BuiltinField FConstructId) (HVLiteral (String (string_of_builtin_function Function_Construct))) in
  let h = add_field h (BLoc LFunction) (BuiltinField FClass) (HVLiteral (String "Function")) in
  let h = add_field h (BLoc LFunction) (UserField "length") (HVLiteral (Num 1.)) in
  let h = add_field h (BLoc LFunction) (UserField "prototype") (HVObj (BLoc Lfp)) in
  
  let h = add_field h (BLoc Lfp) (BuiltinField FClass) (HVLiteral (String "Function")) in
  let h = add_field h (BLoc Lfp) (BuiltinField FId) (HVLiteral (String (string_of_builtin_function Function_Prototype_Call))) in
  let h = add_field h (BLoc Lfp) (UserField "length") (HVLiteral (Num 0.)) in
  let h = add_field h (BLoc Lfp) (UserField "constructor") (HVObj (BLoc LFunction)) in
  let h = fold_add_stub_function h Lfp ["apply"; "call"; "bind"] in
  
  let h = add_field h (BLoc Lg) (UserField "Array") (HVObj (BLoc LArray)) in
  let h = add_field h (BLoc LArray) (BuiltinField FId) (HVLiteral (String (string_of_builtin_function Array_Call))) in (* TODO *)
  let h = add_field h (BLoc LArray) (BuiltinField FConstructId) (HVLiteral (String (string_of_builtin_function Array_Construct))) in (* TODO *)
  let h = add_field h (BLoc LArray) (BuiltinField FClass) (HVLiteral (String "Function")) in
  let h = add_field h (BLoc LArray) (UserField "length") (HVLiteral (Num 1.)) in
  let h = add_field h (BLoc LArray) (UserField "prototype") (HVObj (BLoc Lap)) in
  
  let h = add_field h (BLoc Lap) (BuiltinField FClass) (HVLiteral (String "Array")) in
  let h = add_field h (BLoc Lap) (UserField "length") (HVLiteral (Num 0.)) in
  let h = add_field h (BLoc Lap) (UserField "constructor") (HVObj (BLoc LArray)) in

  let h = add_stub_function h LArray "isArray" in
  let h = fold_add_stub_function h Lap
    ["toString"; "toLocaleString"; "concat"; "join"; "pop"; "push"; "reverse"; "shift"; "slice"; "sort"; "splice";
     "unshift"; "indexOf"; "lastIndexOf"; "every"; "some"; "forEach"; "map"; "filter"; "reduce"; "reduceRight"] in
  
  let h = add_field h (BLoc Lg) (UserField "Boolean") (HVObj (BLoc LBoolean)) in
  let h = add_field h (BLoc LBoolean) (BuiltinField FId) (HVLiteral (String (string_of_builtin_function Boolean_Call))) in
  let h = add_field h (BLoc LBoolean) (BuiltinField FConstructId) (HVLiteral (String (string_of_builtin_function Boolean_Construct))) in
  let h = add_field h (BLoc LBoolean) (UserField "length") (HVLiteral (Num 1.)) in
  let h = add_field h (BLoc LBoolean) (UserField "prototype") (HVObj (BLoc Lbp)) in
  let h = add_field h (BLoc LBoolean) (BuiltinField FClass) (HVLiteral (String "Function")) in

  let h = add_field h (BLoc Lbp) (BuiltinField FClass) (HVLiteral (String "Boolean")) in
  let h = add_field h (BLoc Lbp) (BuiltinField FPrimitiveValue) (HVLiteral (Bool false)) in
  let h = add_field h (BLoc Lbp) (UserField "constructor") (HVObj (BLoc LBoolean)) in
  let h = add_builtin_function h Lbp_toString Boolean_Prototype_toString 0. in
  let h = add_field h (BLoc Lbp) (UserField "toString") (HVObj (BLoc Lbp_toString)) in
  let h = add_builtin_function h Lbp_valueOf Boolean_Prototype_valueOf 0. in
  let h = add_field h (BLoc Lbp) (UserField "valueOf") (HVObj (BLoc Lbp_valueOf)) in
  
  let h = add_field h (BLoc Lg) (UserField "Number") (HVObj (BLoc LNumber)) in
  let h = add_field h (BLoc LNumber) (BuiltinField FId) (HVLiteral (String (string_of_builtin_function Number_Call))) in
  let h = add_field h (BLoc LNumber) (UserField "length") (HVLiteral (Num 1.)) in
  let h = add_field h (BLoc LNumber) (BuiltinField FConstructId) (HVLiteral (String (string_of_builtin_function Number_Construct))) in
  let h = add_field h (BLoc LNumber) (UserField "prototype") (HVObj (BLoc Lnp)) in
  let h = add_field h (BLoc LNumber) (BuiltinField FClass) (HVLiteral (String "Function")) in
  let h = add_field h (BLoc LNumber) (UserField "MAX_VALUE") (HVLiteral (Num max_float)) in
  let h = add_field h (BLoc LNumber) (UserField "MIN_VALUE") (HVLiteral (Num 5e-324)) in
  let h = add_field h (BLoc LNumber) (UserField "NaN") (HVLiteral (Num nan)) in
  let h = add_field h (BLoc LNumber) (UserField "NEGATIVE_INFINITY") (HVLiteral (Num neg_infinity)) in
  let h = add_field h (BLoc LNumber) (UserField "POSITIVE_INFINITY") (HVLiteral (Num infinity)) in
  let h = add_field h (BLoc Lnp) (BuiltinField FClass) (HVLiteral (String "Number")) in
  let h = add_field h (BLoc Lnp) (BuiltinField FPrimitiveValue) (HVLiteral (Num 0.)) in
  let h = add_field h (BLoc Lnp) (UserField "constructor") (HVObj (BLoc LNumber)) in
  let h = add_builtin_function h Lnp_toString Number_Prototype_toString 1. in
  let h = add_field h (BLoc Lnp) (UserField "toString") (HVObj (BLoc Lnp_toString)) in
  let h = add_builtin_function h Lnp_valueOf Number_Prototype_valueOf 0. in
  let h = add_field h (BLoc Lnp) (UserField "valueOf") (HVObj (BLoc Lnp_valueOf)) in
  let h = fold_add_stub_function h Lnp ["toLocaleString"; "toFixed"; "toExponential"; "toPrecision"] in

  let h = add_field h (BLoc Lg) (UserField "Math") (HVObj (BLoc LMath)) in
  let h = add_field h (BLoc LMath) (BuiltinField FClass) (HVLiteral (String "Math")) in
  let h = add_field h (BLoc LMath) (UserField "E") (HVLiteral (Num BatFloat.e)) in
  let h = add_field h (BLoc LMath) (UserField "PI") (HVLiteral (Num BatFloat.pi)) in
  let h = add_field h (BLoc LMath) (UserField "LN10") (HVLiteral (Num BatFloat.ln10)) in
  let h = add_field h (BLoc LMath) (UserField "LN2") (HVLiteral (Num BatFloat.ln2)) in
  let h = add_field h (BLoc LMath) (UserField "LOG2E") (HVLiteral (Num BatFloat.log2e)) in
  let h = add_field h (BLoc LMath) (UserField "LOG10E") (HVLiteral (Num BatFloat.log10e)) in
  let h = add_field h (BLoc LMath) (UserField "SQRT1_2") (HVLiteral (Num (sqrt (1. /. 2.)))) in
  let h = add_field h (BLoc LMath) (UserField "SQRT2") (HVLiteral (Num BatFloat.sqrt2)) in
  let h = fold_add_stub_function h LMath
    ["abs"; "acos"; "asin"; "atan"; "atan2"; "ceil"; "cos"; "exp"; "floor"; "log"; "max";
     "min"; "pow"; "random"; "round"; "sin"; "sqrt"; "tan"] in

  let h = add_field h (BLoc Lg) (UserField "String") (HVObj (BLoc LString)) in
  let h = add_field h (BLoc LString) (BuiltinField FId) (HVLiteral (String (string_of_builtin_function String_Call))) in
  let h = add_field h (BLoc LString) (UserField "length") (HVLiteral (Num 1.)) in
  let h = add_field h (BLoc LString) (BuiltinField FConstructId) (HVLiteral (String (string_of_builtin_function String_Construct))) in
  let h = add_field h (BLoc LString) (UserField "prototype") (HVObj (BLoc Lsp)) in
  let h = add_field h (BLoc LString) (BuiltinField FClass) (HVLiteral (String "Function")) in
  let h = add_stub_function h LString "fromCharCode" in

  let h = add_field h (BLoc Lsp) (BuiltinField FClass) (HVLiteral (String "String")) in
  let h = add_field h (BLoc Lsp) (BuiltinField FPrimitiveValue) (HVLiteral (String "")) in
  let h = add_field h (BLoc Lsp) (UserField "constructor") (HVObj (BLoc LString)) in
  let h = add_builtin_function h Lsp_toString String_Prototype_toString 0. in
  let h = add_field h (BLoc Lsp) (UserField "toString") (HVObj (BLoc Lsp_toString)) in
  let h = add_builtin_function h Lsp_valueOf String_Prototype_valueOf 0. in
  let h = add_field h (BLoc Lsp) (UserField "valueOf") (HVObj (BLoc Lsp_valueOf)) in
  let h = fold_add_stub_function h Lsp
    ["charAt"; "charCodeAt"; "concat"; "indexOf"; "lastIndexOf"; "localeCompare"; "match"; "replace"; "search";
     "slice"; "split"; "substring"; "toLowerCase"; "toLocaleLowerCase"; "toUpperCase"; "toLocaleUpperCase"; "trim"] in

  let h = add_stub_constructor h "Date" 7. in
  let h = fold_add_stub_function h (LStub "Date") ["parse"; "UTC"; "now"] in
  let h = fold_add_stub_function h (LStub "DateP")
    ["toString"; "toDateString"; "toTimeString"; "toLocaleString";
     "toLocaleDateString"; "toLocaleTimeString"; "valueOf"; "getTime"; "getFullYear"; "getUTCFullYear"; "getMonth";
     "getUTCMonth"; "getDate"; "getUTCDate"; "getDay"; "getUTCDay"; "getHours"; "getUTCHours"; "getMinutes";
     "getUTCMinutes"; "getSeconds"; "getUTCSeconds"; "getMilliseconds"; "getUTCMilliseconds"; "getTimezoneOffset";
     "setTime"; "setMilliseconds"; "setUTCMilliseconds"; "setSeconds"; "setUTCSeconds"; "setMinutes"; "setUTCMinutes";
     "setHours"; "setUTCHours"; "setDate"; "setUTCDate"; "setMonth"; "setUTCMonth"; "setFullYear"; "setUTCFullYear";
     "toUTCString"; "toISOString"; "toJSON"] in

  let h = add_stub_constructor h "RegExp" 2. in
  let h = fold_add_stub_function h (LStub "RegExpP") ["exec"; "test"; "toString"] in

  (* Error *)
  let h = add_field h (BLoc Lg) (UserField "Error") (HVObj (BLoc LError)) in
  let h = add_field h (BLoc LError) (UserField "length") (HVLiteral (Num 1.)) in
  let h = add_field h (BLoc LError) (BuiltinField FClass) (HVLiteral (String "Function")) in
  let h = add_field h (BLoc LError) (BuiltinField FId) (HVLiteral (String (string_of_builtin_function Error_Call_Construct))) in
  let h = add_field h (BLoc LError) (BuiltinField FConstructId) (HVLiteral (String (string_of_builtin_function Error_Call_Construct))) in
  let h = add_field h (BLoc LError) (UserField "prototype") (HVObj (BLoc Lep)) in

  (* Error Prototype *)
  let h = add_field h (BLoc Lep) (BuiltinField FClass) (HVLiteral (String "Error")) in
  let h = add_field h (BLoc Lep) (UserField "constructor") (HVObj (BLoc LError)) in
  let h = add_field h (BLoc Lep) (UserField "name") (HVLiteral (String "Error")) in
  let h = add_field h (BLoc Lep) (UserField "message") (HVLiteral (String "")) in
  (* let h = add_stub_function h (BLoc Lep) "toString" in *)

  let h = native_error h "EvalError" LEvalError LEvalErrorP EvalError_Call_Construct in
  let h = native_error h "RangeError" LRangeError LRangeErrorP RangeError_Call_Construct in
  let h = native_error h "ReferenceError" LRError Lrep ReferenceError_Call_Construct in
  let h = native_error h "SyntaxError" LSError Lsep SyntaxError_Call_Construct in
  let h = native_error h "TypeError" LTError Ltep TypeError_Call_Construct in
  let h = native_error h "URIError" LURIError LURIErrorP URIError_Call_Construct in

  let h = add_field h (BLoc Lg) (UserField "JSON") (HVObj (BLoc LJSON)) in
  let h = add_field h (BLoc LJSON) (BuiltinField FClass) (HVLiteral (String "JSON")) in
  let h = fold_add_stub_function h LJSON ["parse"; "stringify"] in
  h

let run_with_heap h (fs : function_block AllFunctions.t) (env : function_block AllFunctions.t) : function_state =
  let main_this = VHValue (HVObj (BLoc Lg)) in
  let main_scope_l = Loc (fresh_loc ()) in
  let h = Heap.add main_scope_l Object.empty h in
  run h main_this (VHValue (HVObj main_scope_l)) fs env
  
let run_with_initial_heap (fs : function_block AllFunctions.t) env : function_state =
  let h = initial_heap () in
  run_with_heap h fs env

  

    
