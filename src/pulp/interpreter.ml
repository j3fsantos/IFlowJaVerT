open Pulp_Syntax 
open Pulp_Syntax_Utils
open Pulp_Syntax_Print

exception InterpreterNotImplemented
exception InterpreterStuck of string

module LabelMap = Map.Make ( 
  struct 
    type t = label
    let compare = compare
  end
)

module Stack = Map.Make ( 
  struct 
    type t = variable
    let compare = compare
  end
)

type loc =
  | BLoc of builtin_loc
  | Loc of int

module Heap = Map.Make ( 
  struct 
    type t = loc
    let compare = compare
  end
)

let fresh_int =
  let counter = ref 0 in
  let rec f =
    let v = !counter in
    counter := !counter + 1;
    v
  in f
  
let fresh_loc () : int =
  fresh_int

module Object = Map.Make ( 
  struct 
    type t = string
    let compare = compare
  end
)

type heap_value =
  | HVLiteral of literal
  | HVObj of loc

(* Do I still need this if I always evaluate literal builtin location to hbobj builtin location? Doesn't feel clean to have same things at different places *)
let heap_value_eq v1 v2 =
  match v1, v2 with
    | HVLiteral lit1, HVLiteral lit2 -> lit1 == lit2
    | HVObj l1, HVObj l2 -> l1 == l2
    | HVLiteral (LLoc l1), HVObj (BLoc l2) -> l1 == l2
    | _, _ -> false

type value =
  | VHValue of heap_value
  | VRef of loc * string * reference_type

let value_eq v1 v2 =
  match v1, v2 with
    | VHValue hv1, VHValue hv2 -> heap_value_eq hv1 hv2
    | VRef (l1, s1, rt1), VRef (l2, s2, rt2) -> l1 == l2 && s1 == s2 && rt1 == rt2
    | _, _ -> false

let heap_value_arith op v1 v2 =
  match v1, v2 with
    |  HVLiteral (Num n1),  HVLiteral (Num n2) -> 
      begin match op with
        | Plus -> HVLiteral (Num (n1 +. n2))
        | Minus -> HVLiteral (Num (n1 -. n2))
        | Times -> HVLiteral (Num (n1 *. n2))
        | Div -> HVLiteral (Num (n1 /. n2))
      end
    | _, _ -> raise (InterpreterStuck "Arith Op on non-numbers")

let value_arith op v1 v2 = 
  match v1, v2 with
    | (VHValue hv1), (VHValue hv2) -> VHValue (heap_value_arith op hv1 hv2)
    | _, _ -> raise (InterpreterStuck "Arith Op on non-numbers")

let heap_value_bool op v1 v2 =
  match v1, v2 with
     | HVLiteral (Bool b1), HVLiteral (Bool b2) -> 
      begin match op with
        | And -> HVLiteral (Bool (b1 && b2))
        | Or -> HVLiteral (Bool (b1 or b2))
      end
    | _, _ -> raise (InterpreterStuck "Boolean Op on non-boolean values")

let value_bool op v1 v2 =
  match v1, v2 with
    | (VHValue hv1), (VHValue hv2) -> VHValue (heap_value_bool op hv1 hv2)
    | _, _ -> raise (InterpreterStuck "Boolean Op on non-boolean values")

type heap_type = (heap_value Object.t) Heap.t
type stack_type = value Stack.t

let run_bin_op op v1 v2 : value =
  begin match op with
    | Comparison cop ->
      begin match cop with
        | Equal -> VHValue (HVLiteral (Bool (value_eq v1 v2)))
      end
    | Arith aop -> value_arith aop v1 v2
    | Boolean bop -> value_bool bop v1 v2
  end
  
let bool_not v =
  match v with
    | VHValue (HVLiteral (Bool (b))) -> VHValue (HVLiteral (Bool (not b)))
    | _ -> raise (InterpreterStuck "Not on non-boolean value")
  
let run_unary_op op v : value =
  match op with
    | Not -> bool_not v

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
      begin match pt with
        | ReferenceType _ -> true
        | _ -> false
      end
    | _ -> pt == vtype

let object_check v error = 
  match v with
    | VHValue (HVLiteral (LLoc l)) -> BLoc l
    | VHValue (HVObj l) -> l
    | _ -> raise (InterpreterStuck error)

let string_check v error = 
  match v with
    | VHValue (HVLiteral (String x)) -> x
    | _ -> raise (InterpreterStuck error)

let object_field_check v1 v2 h error_obj error_field =
	  let l = object_check v1 error_obj in
	  let x = string_check v2 error_field in
    (l, x, Heap.find l h)
    
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
    | Label l -> l == ctx.label_return || l == ctx.label_throw
    | _ -> false
  
let rec run_expr (s : local_state) (e : expression) : value =
  match e with
	  | Literal l ->
      begin match l with
        | LLoc bl -> VHValue (HVObj (BLoc bl))
        | _ -> VHValue (HVLiteral l)
      end
	  | Var v -> Stack.find v s.lsstack
	  | BinOp (e1, op, e2) -> 
      let v1 = run_expr s e1 in
      let v2 = run_expr s e2 in
      run_bin_op op v1 v2
	  | UnaryOp (op, e) -> 
      let v1 = run_expr s e in
      run_unary_op op v1
	  | Ref (e1, e2, rt) -> 
      let l = run_expr s e1 in
      let x = run_expr s e2 in
      let lobj = object_check l "First element of reference should be object" in
      let xstring = string_check x "Second element of reference should be string" in
      VRef (lobj, xstring, rt)
	  | Base e -> 
      let v = run_expr s e in
      begin match v with
        | VRef (l, x, rt) -> VHValue (HVObj l)
        | _ -> raise (InterpreterStuck "Base is only defined on references")
      end
	  | Field e ->       
      let v = run_expr s e in
      begin match v with
        | VRef (l, x, rt) -> VHValue (HVLiteral (String x))
        | _ -> raise (InterpreterStuck "Field is only defined on references")
      end
	  | IsTypeOf (e, pt) -> 
      let v = run_expr s e in
      let b = is_type_of v pt in
      VHValue (HVLiteral (Bool b))
      
let rec get_value_proto v x h =
  match v with
    (* Should it be undefined descriptor? *)
    | VHValue (HVLiteral Null) -> VHValue (HVLiteral Undefined)
    | _ ->
		  begin 
		    try
          let l = object_check v "First argument of Proto must be an object" in
		      let obj = Heap.find l h in
		        begin 
		        try
		            let v = Object.find x obj in VHValue v
		          with
		            | Not_found -> 
		              begin
		                try 
		                  let proto = Object.find (string_of_builtin_field FProto) obj in
		                  get_value_proto (VHValue proto) x h
		                with
		                  | Not_found -> raise (InterpreterStuck "Object must have prototype in Proto")
		              end
		        end
		    with
		      | Not_found -> raise (InterpreterStuck "Object must exists for Proto")
		  end   
      
(* TODO -- I don't like the code here *)
let rec run_assign_expr (s : local_state) (e : assign_right_expression) (funcs : function_block AllFunctions.t) : local_state * value =
	(* Assignment expressions *)
  match e with
	  | Call c -> 
      let fid = run_expr s c.call_name in
      let fid_string = string_check fid "Function name should be a string" in
      let fblock = 
        try AllFunctions.find fid_string funcs 
        with | Not_found -> raise (InterpreterStuck ("Cannot find the function by name" ^ fid_string))
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
      begin 
        try
          let l, x, obj = object_field_check v1 v2 s.lsheap "First argument of HasField must be an object" "Second argument of HasField must be a string" in
	        begin 
            try
	            let _ = Object.find x obj in s, VHValue (HVLiteral (Bool true))
	          with
	            | Not_found -> s, VHValue (HVLiteral (Bool false))
	        end
        with
          | Not_found -> raise (InterpreterStuck "Object must exists for HasField")
      end
	  | Lookup (e1, e2) -> 
      let v1 = run_expr s e1 in
      let v2 = run_expr s e2 in
      begin 
        try
            let l, x, obj = object_field_check v1 v2 s.lsheap "First argument of Lookup must be an object" "Second argument of Lookup must be a string" in
            begin 
            try
                let v = Object.find x obj in s, (VHValue v)
              with
                | Not_found -> raise (InterpreterStuck "Couldn't proceed with Lookup")
            end
        with
          | Not_found -> raise (InterpreterStuck "Object must exists for Lookup")
      end     
	  | Deallocation (e1, e2) -> 
      let v1 = run_expr s e1 in
      let v2 = run_expr s e2 in
      begin 
        try
            let l, x, obj = object_field_check v1 v2 s.lsheap "First argument of Deallocation must be an object" "Second argument of Deallocation must be a string" in
            begin 
            try
                let _ = Object.find x obj in 
                let newobj = Object.remove x obj in
                {s with lsheap = Heap.add l newobj s.lsheap}, VHValue (HVLiteral (Bool true))
              with
                | Not_found -> raise (InterpreterStuck "Couldn't proceed with Deallocation")
            end
        with
          | Not_found -> raise (InterpreterStuck "Object must exists for Deallocation")
      end   
	  | Pi (e1, e2) -> 
      let v1 = run_expr s e1 in
      let v2 = run_expr s e2 in
      begin 
        try
            let l, x, obj = object_field_check v1 v2 s.lsheap "First argument of Proto must be an object" "Second argument of Proto must be a string" in
            let v = get_value_proto (VHValue (HVObj l)) x s.lsheap in s, v
        with
          | Not_found -> raise (InterpreterStuck "Object must exists for Proto")
      end   
and
run_function (h : heap_type) (f : function_block) (args : value list) (fs : function_block AllFunctions.t) : function_state =
  let s = List.fold_left2 (fun st param arg -> Stack.add param arg st) Stack.empty f.func_params args in
    
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
    if l == f.func_ctx.label_return then FTReturn, Stack.find f.func_ctx.return_var result.lsstack
    else if l == f.func_ctx.label_throw then FTException, Stack.find f.func_ctx.throw_var result.lsstack
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
        | _ -> raise (InterpreterStuck "GuardedGoto expression must evaluate to boolean value")
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
      begin 
        try
            let l, x, obj = object_field_check v1 v2 s.lsheap "First argument of Mutation must be an object" "Second argument of Mutation must be a string" in
            let v3 = match v3 with
              | VHValue v -> v
              | VRef _ -> raise (InterpreterStuck "Right hand side of mutation cannot be a reference") in
            let newobj = Object.add x v3 obj in
            {s with lsheap = Heap.add l newobj s.lsheap}
        with
          | Not_found -> raise (InterpreterStuck "Object must exists for Deallocation")
      end  
    | Sugar sss -> raise InterpreterNotImplemented

and run_stmts stmts ctx lstate labelmap fs =
  let next_stmt = List.nth stmts lstate.lscounter in
  if end_label next_stmt labelmap ctx then lstate 
  else 
    let state = run_stmt lstate ctx.label_throw next_stmt labelmap fs in
    run_stmts stmts ctx state labelmap fs

let run (h: heap_type) (fs : function_block AllFunctions.t) : function_state = 
  let main = AllFunctions.find main_fun_id fs in
  run_function h main [] fs
  

    