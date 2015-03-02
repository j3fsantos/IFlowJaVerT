open Batteries
open Pulp_Syntax 
open Pulp_Syntax_Utils
open Pulp_Syntax_Print
open Memory_Model
open Interpreter_Print

exception InterpreterNotImplemented
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
        | Or -> HVLiteral (Bool (b1 or b2))
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

let type_less_than t1 t2 =
  match t2 with
    | ReferenceType None -> 
      begin match t1 with
        | ReferenceType (Some _) -> true
        | _ -> false
      end
    | ObjectType None -> 
      begin match t1 with
        | ObjectType (Some _) -> true
        | _ -> false
      end
    | _ -> false

let value_less_than v1 v2 counter =
  match v1, v2 with
    | VHValue hv1, VHValue hv2 -> heap_value_less_than hv1 hv2 counter
    | VRef (l1, s1, rt1), VRef (l2, s2, rt2) -> false
    | VType t1, VType t2 -> type_less_than t1 t2
    | _, _ -> false

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

let int32_left_shift = (fun x y -> Int32.to_float (Int32.shift_left (Int32.of_float x) (int_of_float y)))

let int32_right_shift = (fun x y -> Int32.to_float (Int32.shift_right (Int32.of_float x) (int_of_float y)))

let uint32_right_shift = (fun x y ->
  let i31 = 2. ** 31. in
  let i32 = 2. ** 32. in
  let newx = if x >= i31 then x -. i32 else x in
  let r = Int32.to_float (Int32.shift_right_logical (Int32.of_float newx) (int_of_float y)) in
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

let float_to_string_inner n = (* TODO *)
  let string_of_number n =
    let inum = int_of_float n in
    if (float_of_int inum = n) then string_of_int inum else string_of_float n in
  if Float.is_nan n then "NaN"
  else if n = 0.0 or n = -0.0 then "0"
  else if n = Float.infinity then "Infinity"
  else string_of_number n

let num_to_string v counter =
  match v with
    | VHValue (HVLiteral (Num n)) -> VHValue (HVLiteral (String (float_to_string_inner n))) 
    | _ -> raise (InterpreterStuck ("Cannot proceed with num_to_string on not number value", counter))

let string_to_num v counter =
  match v with
    | VHValue (HVLiteral (String s)) -> VHValue (HVLiteral (Num (Float.of_string s))) 
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
  match l with
    | LLoc _ -> ObjectType (Some Builtin)
	  | Null -> NullType               
	  | Bool _ -> BooleanType         
	  | Num _ -> NumberType          
	  | String _ -> StringType
	  | Undefined -> UndefinedType
	  | Empty -> UndefinedType (*TODO*)
    | Type _ -> StringType (* TODO *)

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

let is_type_of v pt =
  let vtype = type_of v in
  (*Printf.printf "VType = %s\n" (Pulp_Syntax_Print.string_of_pulp_type vtype);*)
  match pt with
    | ReferenceType None -> 
      begin match vtype with
        | ReferenceType _ -> true
        | _ -> false
      end
    | ObjectType None -> 
      begin match vtype with
        | ObjectType _ -> true
        | _ -> false
      end
    | _ -> pt = vtype

let object_check v error counter = 
  match v with
    | VHValue (HVLiteral (LLoc l)) -> BLoc l
    | VHValue (HVObj l) -> l
    | _ -> raise (InterpreterStuck (error, counter))

let string_check v error counter = 
  match v with
    | VHValue (HVLiteral (String x)) -> x
    | _ -> raise (InterpreterStuck (error, counter))

let object_field_check v1 v2 h cmd_name counter = 
	  let l = object_check v1 ("First argument of " ^ cmd_name ^ " must be an object") counter in
	  let x = string_check v2 ("Second argument of " ^ cmd_name ^ " must be a string") counter in
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
  match stmt with
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
      let xstring = string_check x "Second element of reference should be string" s.lscounter in
      VRef (hv, xstring, rt)
	  | Base e -> 
      let v = run_expr s e in
      begin match v with
        | VRef (v, x, rt) -> VHValue v
        | _ -> raise (InterpreterStuck ("Base is only defined on references", s.lscounter))
      end
	  | Field e ->       
      let v = run_expr s e in
      begin match v with
        | VRef (l, x, rt) -> VHValue (HVLiteral (String x))
        | _ -> raise (InterpreterStuck ("Field is only defined on references", s.lscounter))
      end
	  | IsTypeOf (e, pt) -> 
      let v = run_expr s e in
      let b = is_type_of v pt in
      VHValue (HVLiteral (Bool b))
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
		      let proto = Object.find (string_of_builtin_field FProto) obj in
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
			      let proto = Object.find (string_of_builtin_field FProto) obj in
			      is_proto_obj (VHValue proto) o h counter
			    with
			      | Not_found -> raise (InterpreterStuck ("Object must have prototype in proto_obj", counter))
			end 
      
(* TODO -- I don't like the code here *)
let rec run_assign_expr (s : local_state) (e : assign_right_expression) (funcs : function_block AllFunctions.t) : local_state * value =
  let run_call c builtin =
      let fid = run_expr s c.call_name in
      let fid_string = string_check fid "Function name should be a string" s.lscounter in
      let fblock = 
        try AllFunctions.find fid_string funcs 
        with | Not_found -> raise (InterpreterStuck ("Cannot find the function by name" ^ fid_string, s.lscounter))
      in  
      let vthis = run_expr s c.call_this in
      let vscope = run_expr s c.call_scope in
      let vargs = List.map (run_expr s) c.call_args in
      let fs = run_function s.lsheap fblock ([vthis; vscope] @ vargs) funcs builtin in
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
             
     let exp = Parser_main.exp_from_string varg in  
    
     (* TODO update all_functions *)
     let eval_main = fresh_named "eval" in
     let pexp = Pulp_Translate.exp_to_pulp Pulp_Translate.IVL_goto exp eval_main in
    
     let funcs = AllFunctions.fold (fun key value result -> AllFunctions.add key value result) pexp funcs in
      
     let main = AllFunctions.find eval_main pexp in  
   
      let fs = run_function s.lsheap main ([vthis; vscope]) funcs true in
      begin match fs.fs_return_type with
        | FTException -> {s with lsheap = fs.fs_heap; lsexcep = Some (c.call_throw_label)}, fs.fs_return_value
        | FTReturn -> {s with lsheap = fs.fs_heap}, fs.fs_return_value
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
			let l, x, obj = object_field_check v1 v2 s.lsheap "proto_field" s.lscounter in
			let v = get_value_proto (VHValue (HVObj l)) x s.lsheap s.lscounter in s, v 
      
   | ProtoO (e1, e2) -> 
      let v1 = run_expr s e1 in
      let v2 = run_expr s e2 in 
      let l1 = object_check v1 "proto_obj" s.lscounter in
      let l2 = object_check v2 "proto_obj" s.lscounter in
      let v = is_proto_obj (VHValue (HVObj l1)) l2 s.lsheap s.lscounter in s, v 
and
run_function (h : heap_type) (f : function_block) (args : value list) (fs : function_block AllFunctions.t) (is_builtin) : function_state =
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
    match stmt with
      | Label l -> (index + 1, LabelMap.add l index li)
      | _ -> index + 1, li
    ) (0, LabelMap.empty) f.func_body in
    
  let result = run_stmts f.func_body f.func_ctx {lsheap = h; lsstack = s; lscounter = 0; lsexcep = None} label_index fs in
  (*Printf.printf "End of function %s \n" f.func_name;*)
  let ret_type, ret_val = 
    let stmt = List.nth f.func_body result.lscounter in
    let l = match stmt with
      | Label l -> l
      | _ -> raise (Invalid_argument "Shouldn't be other stametemnt than Label statemment here") in
    if l = f.func_ctx.label_return then FTReturn, 
       (try Stack.find f.func_ctx.return_var result.lsstack 
        with Not_found -> raise (InterpreterStuck ("Cannot find return variable", result.lscounter)))
    else if l = f.func_ctx.label_throw then FTException, 
       (try Stack.find f.func_ctx.throw_var result.lsstack
        with Not_found -> raise (InterpreterStuck ("Cannot find throw variable", result.lscounter)))
    else raise (Invalid_argument "Shouldn't be other label than end label here")
  in 
  {fs_heap = result.lsheap; fs_return_type = ret_type; fs_return_value = ret_val}
  
and run_basic_stmt (s : local_state) (stmt : basic_statement) (labelmap : int LabelMap.t) (fs : function_block AllFunctions.t) : local_state =
   match stmt with
    | Skip -> {s with lscounter = s.lscounter + 1}
    | Assignment assign -> 
      let s, v = run_assign_expr s assign.assign_right fs in
      begin match s.lsexcep with
        | Some throwl ->
        {s with 
          lsstack = Stack.add assign.assign_left v s.lsstack; 
          lscounter = LabelMap.find throwl labelmap;
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

and run_stmt (s : local_state) (stmt : statement) (labelmap : int LabelMap.t) (fs : function_block AllFunctions.t) : local_state =
  (*Printf.printf "Running stmt %s \n" (Pulp_Syntax_Print.string_of_statement stmt);*)
  match stmt with
    | Label l -> {s with lscounter = s.lscounter + 1}
    | Goto l -> {s with lscounter = LabelMap.find l labelmap}
    | GuardedGoto (e, l1, l2) -> 
      let v = run_expr s e in
      begin match v with
        | VHValue (HVLiteral (Bool true)) ->
          {s with lscounter = LabelMap.find l1 labelmap}
        | VHValue (HVLiteral (Bool false)) ->
          {s with lscounter = LabelMap.find l2 labelmap}
        | _ -> raise (InterpreterStuck ("GuardedGoto expression must evaluate to boolean value", s.lscounter))
      end
    | Basic bs -> run_basic_stmt s bs labelmap fs
    | Sugar sss -> raise InterpreterNotImplemented

and run_stmts stmts ctx lstate labelmap fs =
  let next_stmt = List.nth stmts lstate.lscounter in
  if end_label next_stmt labelmap ctx then lstate 
  else 
    let state = run_stmt lstate next_stmt labelmap fs in
    run_stmts stmts ctx state labelmap fs
    
let run (h: heap_type) main_this main_scope (fs : function_block AllFunctions.t) : function_state = 
  let main = AllFunctions.find main_fun_id fs in
  run_function h main [main_this; main_scope] fs false
  
let built_in_obj_proto_lop h obj =
  let l = Object.add (string_of_builtin_field FProto) (HVObj (BLoc Lop)) Object.empty in
  Heap.add (BLoc obj) l h
  
let built_in_obj_proto_lfp h obj =
  let l = Object.add (string_of_builtin_field FProto) (HVObj (BLoc Lfp)) Object.empty in
  Heap.add (BLoc obj) l h
  
let add_field h l f v =
  let obj = Heap.find l h in
  let obj = Object.add f v obj in
  Heap.add l obj h
    
let initial_heap () =
  let h = Heap.empty in
  let lop = Object.add (string_of_builtin_field FProto) (HVLiteral Null) Object.empty in
  let h = Heap.add (BLoc Lop) lop h in
  (* Do I want Error object too? Rather then going directly to Lop for errors *)
  let h = List.fold_left built_in_obj_proto_lop h [Lg; Lfp; LEval; LRError; LSError; 
    LNotImplemented GetValuePrim; LNotImplemented ToNumber; LNotImplemented ToString; Lbp; Lnp; Lsp; Lep] in
  let h = List.fold_left built_in_obj_proto_lfp h [LObject; LBoolean; LNumber; LString; LError; LTError] in
    
  let l_lop_toString =  Object.add (string_of_builtin_field FId) (HVLiteral (String (string_of_builtin_function Object_Prototype_toString))) Object.empty in 
  let h = Heap.add (BLoc Lop_toString) l_lop_toString h in
  let h = add_field h (BLoc Lop) "toString" (HVObj (BLoc Lop_toString)) in
  let l_lop_valueOf =  Object.add (string_of_builtin_field FId) (HVLiteral (String (string_of_builtin_function Object_Prototype_valueOf))) Object.empty in 
  let h = Heap.add (BLoc Lop_valueOf) l_lop_valueOf h in
  let h = add_field h (BLoc Lop) "valueOf" (HVObj (BLoc Lop_valueOf)) in
  let l_lop_isPrototypeOf =  Object.add (string_of_builtin_field FId) (HVLiteral (String (string_of_builtin_function Object_Prototype_isPrototypeOf))) Object.empty in 
  let h = Heap.add (BLoc Lop_isPrototypeOf) l_lop_isPrototypeOf h in
  let h = add_field h (BLoc Lop) "isPrototypeOf" (HVObj (BLoc Lop_isPrototypeOf)) in
  let h = add_field h (BLoc Lop) ("constructor") (HVObj (BLoc LObject)) in
    
  let h = add_field h (BLoc Lg) "eval" (HVObj (BLoc LEval)) in
  let h = add_field h (BLoc Lg) "undefined" (HVLiteral Undefined) in
  let h = add_field h (BLoc Lg) "NaN" (HVLiteral (Num nan)) in
  let h = add_field h (BLoc Lg) "Infinity" (HVLiteral (Num infinity)) in
  let h = Heap.add (BLoc LEval) Object.empty h in
  let h = add_field h (BLoc LEval) (string_of_builtin_field FId) (HVLiteral (String ("eval"))) in
  
  let h = add_field h (BLoc Lg) "Object" (HVObj (BLoc LObject)) in
  let h = add_field h (BLoc LObject) (string_of_builtin_field FId) (HVLiteral (String (string_of_builtin_function Object_Call))) in
  let h = add_field h (BLoc LObject) (string_of_builtin_field FConstructId) (HVLiteral (String (string_of_builtin_function Object_Construct))) in
  let l_obj_get_proto_of =  Object.add (string_of_builtin_field FId) (HVLiteral (String (string_of_builtin_function Object_getPrototypeOf))) Object.empty in
  let h = Heap.add (BLoc LObjectGetPrototypeOf) l_obj_get_proto_of h in 
  let h = add_field h (BLoc LObject) "getPrototypeOf" (HVObj (BLoc LObjectGetPrototypeOf)) in
  let h = add_field h (BLoc LObject) (string_of_builtin_field FPrototype) (HVObj (BLoc Lop)) in
  
  let h = add_field h (BLoc Lg) "Boolean" (HVObj (BLoc LBoolean)) in
  let h = add_field h (BLoc LBoolean) (string_of_builtin_field FId) (HVLiteral (String (string_of_builtin_function Boolean_Call))) in
  let h = add_field h (BLoc LBoolean) (string_of_builtin_field FConstructId) (HVLiteral (String (string_of_builtin_function Boolean_Construct))) in
  let h = add_field h (BLoc LBoolean) (string_of_builtin_field FPrototype) (HVObj (BLoc Lbp)) in
  let h = add_field h (BLoc Lbp) ("constructor") (HVObj (BLoc LBoolean)) in
  let l_lbp_toString =  Object.add (string_of_builtin_field FId) (HVLiteral (String (string_of_builtin_function Boolean_Prototype_toString))) Object.empty in 
  let h = Heap.add (BLoc Lbp_toString) l_lbp_toString h in
  let h = add_field h (BLoc Lbp) "toString" (HVObj (BLoc Lbp_toString)) in
  let l_lbp_valueOf =  Object.add (string_of_builtin_field FId) (HVLiteral (String (string_of_builtin_function Boolean_Prototype_valueOf))) Object.empty in 
  let h = Heap.add (BLoc Lbp_valueOf) l_lbp_valueOf h in
  let h = add_field h (BLoc Lbp) "valueOf" (HVObj (BLoc Lbp_valueOf)) in
  
  let h = add_field h (BLoc Lg) "Number" (HVObj (BLoc LNumber)) in
  let h = add_field h (BLoc LNumber) (string_of_builtin_field FId) (HVLiteral (String (string_of_builtin_function Number_Call))) in
  let h = add_field h (BLoc LNumber) (string_of_builtin_field FConstructId) (HVLiteral (String (string_of_builtin_function Number_Construct))) in
  let h = add_field h (BLoc LNumber) (string_of_builtin_field FPrototype) (HVObj (BLoc Lnp)) in
  let h = add_field h (BLoc LNumber) ("MAX_VALUE") (HVLiteral (Num max_float)) in
  let h = add_field h (BLoc LNumber) ("MIN_VALUE") (HVLiteral (Num min_float)) in
  let h = add_field h (BLoc LNumber) "NaN" (HVLiteral (Num nan)) in
  let h = add_field h (BLoc LNumber) ("NEGATIVE_INFINITY") (HVLiteral (Num neg_infinity)) in
  let h = add_field h (BLoc LNumber) ("POSITIVE_INFINITY") (HVLiteral (Num infinity)) in
  let h = add_field h (BLoc Lnp) (string_of_builtin_field FClass) (HVLiteral (String "Number")) in
  let h = add_field h (BLoc Lnp) ("constructor") (HVObj (BLoc LNumber)) in
  let l_lnp_toString =  Object.add (string_of_builtin_field FId) (HVLiteral (String (string_of_builtin_function Number_Prototype_toString))) Object.empty in 
  let h = Heap.add (BLoc Lnp_toString) l_lnp_toString h in
  let h = add_field h (BLoc Lnp) "toString" (HVObj (BLoc Lnp_toString)) in
  let l_lbp_valueOf =  Object.add (string_of_builtin_field FId) (HVLiteral (String (string_of_builtin_function Number_Prototype_valueOf))) Object.empty in 
  let h = Heap.add (BLoc Lnp_valueOf) l_lbp_valueOf h in
  let h = add_field h (BLoc Lnp) "valueOf" (HVObj (BLoc Lnp_valueOf)) in
  
  let h = add_field h (BLoc Lg) "String" (HVObj (BLoc LString)) in
  let h = add_field h (BLoc LString) (string_of_builtin_field FId) (HVLiteral (String (string_of_builtin_function String_Call))) in
  let h = add_field h (BLoc LString) (string_of_builtin_field FConstructId) (HVLiteral (String (string_of_builtin_function String_Construct))) in
  let h = add_field h (BLoc LString) (string_of_builtin_field FPrototype) (HVObj (BLoc Lsp)) in
  let h = add_field h (BLoc Lsp) (string_of_builtin_field FClass) (HVLiteral (String "String")) in
  let h = add_field h (BLoc Lsp) ("constructor") (HVObj (BLoc LString)) in
  let l_lsp_toString =  Object.add (string_of_builtin_field FId) (HVLiteral (String (string_of_builtin_function String_Prototype_toString))) Object.empty in 
  let h = Heap.add (BLoc Lsp_toString) l_lsp_toString h in
  let h = add_field h (BLoc Lsp) "toString" (HVObj (BLoc Lsp_toString)) in
  let l_lsp_valueOf =  Object.add (string_of_builtin_field FId) (HVLiteral (String (string_of_builtin_function String_Prototype_valueOf))) Object.empty in 
  let h = Heap.add (BLoc Lsp_valueOf) l_lsp_valueOf h in
  let h = add_field h (BLoc Lsp) "valueOf" (HVObj (BLoc Lsp_valueOf)) in
  
  let h = add_field h (BLoc Lg) "Error" (HVObj (BLoc LError)) in
  let h = add_field h (BLoc LError) (string_of_builtin_field FPrototype) (HVObj (BLoc Lep)) in
  let h = add_field h (BLoc Lg) "TypeError" (HVObj (BLoc LTError)) in
  let h = add_field h (BLoc LTError) (string_of_builtin_field FId) (HVLiteral (String (string_of_builtin_function TypeError_Call))) in
  let h = add_field h (BLoc LTError) (string_of_builtin_field FConstructId) (HVLiteral (String (string_of_builtin_function TypeError_Construct))) in
  let h = add_field h (BLoc LTError) (string_of_builtin_field FPrototype) (HVObj (BLoc Ltep)) in
  let ltep = Object.add (string_of_builtin_field FProto) (HVObj (BLoc Lep)) Object.empty in
  let h = Heap.add (BLoc Ltep) ltep h in
  let h = add_field h (BLoc Ltep) "name" (HVLiteral (String "TypeError")) in
  let h = add_field h (BLoc Ltep) "message" (HVLiteral (String "")) in
  let h = add_field h (BLoc Lg) "ReferenceError" (HVObj (BLoc LRError)) in
  let h = add_field h (BLoc LRError) (string_of_builtin_field FId) (HVLiteral (String (string_of_builtin_function ReferenceError_Call))) in
  let h = add_field h (BLoc LRError) (string_of_builtin_field FConstructId) (HVLiteral (String (string_of_builtin_function ReferenceError_Construct))) in
  let h = add_field h (BLoc LRError) (string_of_builtin_field FPrototype) (HVObj (BLoc Lrep)) in
  let lrep = Object.add (string_of_builtin_field FProto) (HVObj (BLoc Lep)) Object.empty in
  let h = Heap.add (BLoc Lrep) lrep h in
  let h = add_field h (BLoc Lrep) "name" (HVLiteral (String "ReferenceError")) in
  let h = add_field h (BLoc Lrep) "message" (HVLiteral (String "")) in
  let h = add_field h (BLoc Lep) "name" (HVLiteral (String "Error")) in
  let h = add_field h (BLoc Lep) "message" (HVLiteral (String "")) in
  h
  
let run_with_heap h (fs : function_block AllFunctions.t) : function_state =
  let main_this = VHValue (HVObj (BLoc Lg)) in
  let main_scope_l = Loc (fresh_loc ()) in
  let h = Heap.add main_scope_l Object.empty h in
  run h main_this (VHValue (HVObj main_scope_l)) fs
  
let run_with_initial_heap (fs : function_block AllFunctions.t) : function_state =
  let h = initial_heap () in
  run_with_heap h fs

  

    