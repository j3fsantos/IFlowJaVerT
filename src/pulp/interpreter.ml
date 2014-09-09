open Pulp_Syntax 
open Pulp_Syntax_Utils

exception InterpreterNotImplemented

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

module Object = Map.Make ( 
  struct 
    type t = string
    let compare = compare
  end
)

type value =
  | VLiteral of literal
  | VRef of loc * string * reference_type

type heap_type = (value Object.t) Heap.t
type stack_type = value Stack.t

type local_state = {
  lsheap : heap_type;
  lsstack : stack_type;
  lscounter : int
}

type function_return_type =
  | Normal
  | Exception
  | Return
  
let run_expr (s : local_state) (e : expression) : local_state =
  match e with
	  | Literal l -> raise InterpreterNotImplemented
	  | Var v -> raise InterpreterNotImplemented
	  | BinOp (e1, op, e2) -> raise InterpreterNotImplemented
	  | UnaryOp (op, e) -> raise InterpreterNotImplemented
	  | Ref (e1, e2, rt) -> raise InterpreterNotImplemented
	  | Base e -> raise InterpreterNotImplemented
	  | Field e -> raise InterpreterNotImplemented
	  | IsTypeOf (e, pt) -> raise InterpreterNotImplemented
	  (* Assignment expressions *)
	  | Call c -> raise InterpreterNotImplemented
	  | Obj -> raise InterpreterNotImplemented
	  | HasField (e1, e2) -> raise InterpreterNotImplemented
	  | Lookup (e1, e2) -> raise InterpreterNotImplemented
	  | Deallocation (e1, e2) -> raise InterpreterNotImplemented
	  | Pi (e1, e2) -> raise InterpreterNotImplemented

let run_stmt (s : local_state) (stmt : statement) (labelmap : int LabelMap.t) : local_state =
  match stmt with
    | Skip -> {s with lscounter = s.lscounter + 1}
    | Label l -> {s with lscounter = s.lscounter + 1}
    | Goto l -> {s with lscounter = LabelMap.find l labelmap}
    | GuardedGoto (e, l1, l2) -> raise InterpreterNotImplemented
    | Assume e -> raise InterpreterNotImplemented
    | Assert e -> raise InterpreterNotImplemented
    | Assignment assign -> raise InterpreterNotImplemented
    | Mutation m -> raise InterpreterNotImplemented
    | Sugar sss -> raise InterpreterNotImplemented

let end_label stmt labelmap ctx =
  match stmt with
    | Label l -> l == ctx.label_end || l == ctx.label_return || l == ctx.label_throw
    | _ -> false

let rec run_stmts stmts ctx lstate labelmap =
  let next_stmt = List.nth stmts lstate.lscounter in
  if end_label next_stmt labelmap ctx then lstate 
  else 
    let state = run_stmt lstate next_stmt labelmap in
    run_stmts stmts ctx state labelmap

type function_state = {
    fs_heap : heap_type;
    fs_return_type : function_return_type;
    fs_return_value : value 
}
    
let run_function (h : heap_type) (f : function_block) (args : value list) (fs : function_block AllFunctions.t) : function_state =
  let s = List.fold_left2 (fun st param arg -> Stack.add param arg st) Stack.empty f.func_params args in
    
  let _, label_index = List.fold_left (fun (index, li) stmt ->
    match stmt with
      | Label l -> (index + 1, LabelMap.add l index li)
      | _ -> index + 1, li
    ) (0, LabelMap.empty) f.func_body in
    
  let result = run_stmts f.func_body f.func_ctx {lsheap = h; lsstack = s; lscounter = 0} label_index in
  
  let ret_type, ret_val = 
    let stmt = List.nth f.func_body result.lscounter in
    let l = match stmt with
      | Label l -> l
      | _ -> raise (Invalid_argument "Shouldn't be other stametemnt than Label statemment here") in
    if l == f.func_ctx.label_end then Normal, Stack.find f.func_ctx.end_var result.lsstack
    else if l == f.func_ctx.label_return then Return, Stack.find f.func_ctx.return_var result.lsstack
    else if l == f.func_ctx.label_throw then Exception, Stack.find f.func_ctx.throw_var result.lsstack
    else raise (Invalid_argument "Shouldn't be other label than end label here")
  in
  
  {fs_heap = result.lsheap; fs_return_type = ret_type; fs_return_value = ret_val}
  

let run (h: heap_type) (fs : function_block AllFunctions.t) : function_state = 
  let main = AllFunctions.find main_fun_id fs in
  run_function h main [] fs
  

    