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

let run_bin_op op v1 v2 counter : value =
  begin match op with
    | Comparison cop ->
      begin match cop with
        | Equal -> VHValue (HVLiteral (Bool (value_eq v1 v2)))
      end
    | Arith aop -> value_arith aop v1 v2 counter
    | Boolean bop -> value_bool bop v1 v2 counter
  end
  
let to_boolean v counter =
  match v with
    | HVLiteral lit ->
      begin match lit with
        | LLoc _ -> true
			  | Null -> false                  
			  | Bool b -> b         
			  | Num n -> 
          begin match Float.classify n with
            | FP_zero
            | FP_nan -> false
            | _ -> true    
          end  
			  | String s -> not (s = "")
			  | Undefined -> false
			  | Empty -> raise (InterpreterStuck ("Cannot proceed with ! on empty value", counter))
      end
    | HVObj _ -> true
  
let bool_not v counter =
  match v with
    | VHValue hv -> VHValue (HVLiteral (Bool (not (to_boolean hv counter))))
    | _ -> raise (InterpreterStuck ("Cannot proceed with ! on reference value", counter))
  
let run_unary_op op v counter : value =
  match op with
    | Not -> bool_not v counter 

let type_of_literal l =
  match l with
    | LLoc _ -> ObjectType
	  | Null -> NullType               
	  | Bool _ -> BooleanType         
	  | Num _ -> NumberType          
	  | String _ -> StringType
	  | Undefined
	  | Empty -> UndefinedType

let type_of v =
  match v with
    | VHValue hv ->
      begin match hv with
        | HVLiteral lit -> type_of_literal lit
        | HVObj _ -> ObjectType
      end
    | VRef (_, _, rt) -> ReferenceType (Some rt)

let is_type_of v pt =
  let vtype = type_of v in
  match pt with
    | ReferenceType None -> 
      begin match vtype with
        | ReferenceType _ -> true
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
  lsexcep : bool;
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
      
let rec get_value_proto v x h counter =
  match v with
    (* Should it be undefined descriptor? *)
    | VHValue (HVLiteral Null) -> VHValue (HVLiteral Undefined)
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
		    
      
(* TODO -- I don't like the code here *)
let rec run_assign_expr (s : local_state) (e : assign_right_expression) (funcs : function_block AllFunctions.t) : local_state * value =
	(* Assignment expressions *)
  match e with
	  | Call c -> 
      let fid = run_expr s c.call_name in
      let fid_string = string_check fid "Function name should be a string" s.lscounter in
      let fblock = 
        try AllFunctions.find fid_string funcs 
        with | Not_found -> raise (InterpreterStuck ("Cannot find the function by name" ^ fid_string, s.lscounter))
      in  
      let vthis = run_expr s c.call_this in
      let vscope = run_expr s c.call_scope in
      let vargs = List.map (run_expr s) c.call_args in
      let fs = run_function s.lsheap fblock ([vthis; vscope] @ vargs) funcs in
      begin match fs.fs_return_type with
        | FTException -> {s with lsheap = fs.fs_heap; lsexcep = true}, fs.fs_return_value
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

	  | Pi (e1, e2) -> 
      let v1 = run_expr s e1 in
      let v2 = run_expr s e2 in	
			let l, x, obj = object_field_check v1 v2 s.lsheap "Proto" s.lscounter in
			let v = get_value_proto (VHValue (HVObj l)) x s.lsheap s.lscounter in s, v 
and
run_function (h : heap_type) (f : function_block) (args : value list) (fs : function_block AllFunctions.t) : function_state =
  let s = List.fold_left2 (fun st param arg -> Stack.add param arg st) Stack.empty f.func_params args in
  let s = Stack.add f.func_ctx.return_var (VHValue (HVLiteral Empty)) s in
  let s = Stack.add f.func_ctx.throw_var (VHValue (HVLiteral Empty)) s in
    
  let _, label_index = List.fold_left (fun (index, li) stmt ->
    match stmt with
      | Label l -> (index + 1, LabelMap.add l index li)
      | _ -> index + 1, li
    ) (0, LabelMap.empty) f.func_body in
    
  let result = run_stmts f.func_body f.func_ctx {lsheap = h; lsstack = s; lscounter = 0; lsexcep = false} label_index fs in
  
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

and run_stmt (s : local_state) (throw_label : string) (stmt : statement) (labelmap : int LabelMap.t) (fs : function_block AllFunctions.t) : local_state =
  match stmt with
    | Skip -> {s with lscounter = s.lscounter + 1}
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
    | Assume e -> raise InterpreterNotImplemented
    | Assert e -> raise InterpreterNotImplemented
    | Assignment assign -> 
      let s, v = match assign.assign_right with
        | AE ae -> s, run_expr s ae 
        | AER aer -> run_assign_expr s aer fs in
      if s.lsexcep then
        {s with lscounter = LabelMap.find throw_label labelmap}
      else {s with lsstack = Stack.add assign.assign_left v s.lsstack; lscounter = s.lscounter + 1}
    | Mutation m -> 
      let v1 = run_expr s m.m_loc in
      let v2 = run_expr s m.m_field in
      let v3 = run_expr s m.m_right in
			let l, x, obj = object_field_check v1 v2 s.lsheap "Mutation" s.lscounter in
			let v3 = match v3 with
			  | VHValue v -> v
			  | VRef _ -> raise (InterpreterStuck ("Right hand side of mutation cannot be a reference", s.lscounter)) in
			let newobj = Object.add x v3 obj in
			{s with lsheap = Heap.add l newobj s.lsheap; lscounter = s.lscounter + 1}
    | Sugar sss -> raise InterpreterNotImplemented

and run_stmts stmts ctx lstate labelmap fs =
  let next_stmt = List.nth stmts lstate.lscounter in
  if end_label next_stmt labelmap ctx then lstate 
  else 
    let state = run_stmt lstate ctx.label_throw next_stmt labelmap fs in
    run_stmts stmts ctx state labelmap fs
    
let run (h: heap_type) main_this main_scope (fs : function_block AllFunctions.t) : function_state = 
  let main = AllFunctions.find main_fun_id fs in
  run_function h main [main_this; main_scope] fs
  
let built_in_obj_proto_lop h obj =
  let l = Object.add (string_of_builtin_field FProto) (HVObj (BLoc Lop)) Object.empty in
  Heap.add (BLoc obj) l h
    
let initial_heap () =
  let h = Heap.empty in
  let lop = Object.add (string_of_builtin_field FProto) (HVLiteral Null) Object.empty in
  let h = Heap.add (BLoc Lop) lop h in
  (* Do I want Error object too? Rather then going directly to Lop for errors *)
  let h = List.fold_left built_in_obj_proto_lop h [Lg; Lfp; LEval; LRError; LTError; LSError; LNotImplemented] in
  h
  
let run_with_heap h (fs : function_block AllFunctions.t) : function_state =
  let main_this = VHValue (HVObj (BLoc Lg)) in
  let main_scope_l = Loc (fresh_loc ()) in
  let h = Heap.add main_scope_l Object.empty h in
  run h main_this (VHValue (HVObj main_scope_l)) fs
  
let run_with_initial_heap (fs : function_block AllFunctions.t) : function_state =
  let h = initial_heap () in
  run_with_heap h fs

  

    