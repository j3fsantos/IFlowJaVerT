open Pulp_Syntax 
open Pulp_Syntax_Utils

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
      let lobj = 
        match l with
          | VHValue hv ->
            begin match hv with
              | HVLiteral (LLoc l) -> BLoc l
              | HVObj l -> l
              | _ -> raise (InterpreterStuck "First element of reference should be object ")
            end
          | _ -> raise (InterpreterStuck "First element of reference should be object ") in
      let xstring =
        match x with
          | VHValue (HVLiteral (String x)) -> x
          | _ -> raise (InterpreterStuck "Second element of reference should be string ") in
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

let run_assing_expr (s : local_state) (e : assign_right_expression) : local_state * value =
	(* Assignment expressions *)
  match e with
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
  

    