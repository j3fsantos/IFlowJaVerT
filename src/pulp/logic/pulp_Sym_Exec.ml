open Pulp_Syntax
open State_Graph
open Control_Flow
open Logic

exception NotImplemented of string

let execute_basic_stmt bs pre : Logic.formula =
  (* pre => pre_stmt' * F*)
  (* post_stmt' * F *)
  match bs with
    | Skip -> raise (NotImplemented "Skip")
    | Assignment a ->
      begin match a.assign_right with
        | Expression e -> raise (NotImplemented "Expression")
        | Call _ 
        | Eval _
        | BuiltinCall _ -> raise (Invalid_argument "Call")
        | Obj -> raise (NotImplemented "Obj")
        | HasField (e1, e2) -> raise (NotImplemented "HasField")
        | Lookup (e1, e2) -> raise (NotImplemented "Lookup")
        | Deallocation (e1, e2) -> raise (NotImplemented "Deallocation")
        | ProtoF (e1, e2) -> raise (NotImplemented "ProtoField")
        | ProtoO (e1, e2) -> raise (NotImplemented "ProtoObj")
      end
    | Mutation m -> raise (NotImplemented "Mutation")
 

let rec execute_stmt f sg cfg fs snode_id = 
  (* Hashtable cfg_node -> state_node list for termination *)
  let new_snode id state =
    execute_stmt f sg cfg fs (StateG.mk_node sg (mk_sg_node id state)) in
    
  let get_single_succ id =
    let succs = CFG.succ cfg id in
      begin match succs with
        | [succ] -> succ
        | _ -> raise (Invalid_argument "Expected single successor")
      end in
 
  let snode = StateG.get_node_data sg snode_id in
  let stmt = CFG.get_node_data cfg snode.sgn_id in
  
  match stmt with
    | Label l -> 
      if l = f.func_ctx.label_return or l = f.func_ctx.label_throw 
      then () 
      else new_snode (get_single_succ snode.sgn_id) snode.sgn_state
      
    | Goto l -> new_snode (get_single_succ snode.sgn_id) snode.sgn_state
    
    | GuardedGoto (e, l1, l2) -> ()
    | Basic (Assignment {assign_right = (Call {call_throw_label = throwl})})      
    | Basic (Assignment {assign_right = (Eval {call_throw_label = throwl})}) 
    | Basic (Assignment {assign_right = (BuiltinCall {call_throw_label = throwl})}) -> 
      ()
    | Basic bs -> 
      let post = execute_basic_stmt bs snode.sgn_state in
      new_snode (get_single_succ snode.sgn_id) post 
    | Sugar s -> raise (Invalid_argument "Symbolic execution does not work on syntactic sugar")
  
  

let execute f cfg fs spec =
  let nodes = CFG.nodes cfg in
  let start = List.hd nodes in
  
  (* state graph *)
  let sg = StateG.mk_graph () in
  let first = StateG.mk_node sg (mk_sg_node start spec.spec_pre) in
  execute_stmt f sg cfg fs first
  

let execute_all (f : function_block) (fs : function_block AllFunctions.t) : unit = 
  let cfg = fb_to_cfg f in
  List.iter (execute f cfg fs) f.func_spec