open Graphs
open Pulp_Syntax
open Pulp_Procedure
open Simp_Common

module CFG = AbstractGraph (struct type t = statement end) (struct type t = edge_type end)

let get_all_labels g =
  let label_map = Hashtbl.create 100 in
  let _ = List.iter (fun n -> 
    let d = CFG.get_node_data g n in
    match d with
      | Label l -> Hashtbl.add label_map l n
      | _ -> ()
    ) (CFG.nodes g) in
  label_map
  
let connect_calls_throw g label_map node = 
  let stmt = CFG.get_node_data g node in
  match stmt with
    | Basic (Assignment {assign_right = (Call {call_throw_label = throwl})}) -> 
      CFG.mk_edge g node (Hashtbl.find label_map throwl) Edge_Excep
    | Basic (Assignment {assign_right = (Eval {call_throw_label = throwl})}) -> 
      CFG.mk_edge g node (Hashtbl.find label_map throwl) Edge_Excep
    | Basic (Assignment {assign_right = (BuiltinCall {call_throw_label = throwl})}) -> 
      CFG.mk_edge g node (Hashtbl.find label_map throwl) Edge_Excep
    | Sugar (SpecFunction (left, sf, excep_label)) -> 
      CFG.mk_edge g node (Hashtbl.find label_map excep_label) Edge_Excep
    | _ -> ()
  
  
let rec connect_nodes g current nodes label_map = 
  let stmt = CFG.get_node_data g current in
  begin match stmt with
    | Goto l -> 
      let lnode = Hashtbl.find label_map l in
      CFG.mk_edge g current lnode Edge_Normal;
    | GuardedGoto (_, l1, l2) ->
      let lnode1 = Hashtbl.find label_map l1 in
      CFG.mk_edge g current lnode1 Edge_True;
      let lnode2 = Hashtbl.find label_map l2 in
      CFG.mk_edge g current lnode2 Edge_False;
    | _ -> 
      begin match nodes with
        | [] -> ()
        | hd :: tail -> 
          CFG.mk_edge g current hd Edge_Normal;
     end
   end;
   begin match nodes with
    | [] -> ()
    | hd :: tail -> 
      connect_nodes g hd tail label_map
   end
   
let fb_to_cfg fb : CFG.graph = 
  let g = CFG.mk_graph () in
  
  let start = CFG.mk_node g (Label fb.func_ctx.label_entry) in
  
  let nodes = List.map (CFG.mk_node g) (fb.func_body) in
    
  let nodes = List.filter (fun n -> 
     let nd = CFG.get_node_data g n in
     match nd with
      | Label l -> not (l = fb.func_ctx.label_throw || l = fb.func_ctx.label_return)
      | _ -> true
    ) nodes in
 
  let label_map = get_all_labels g in
  connect_nodes g start nodes label_map;
  
  List.iter (connect_calls_throw g label_map) nodes;
  g
  
let program_to_cfg (all_functions : function_block AllFunctions.t) : CFG.graph AllFunctions.t =
  AllFunctions.map fb_to_cfg all_functions
  
  
  
(* Print one cfg at a time *)  
let print_cfg (cfgs : CFG.graph AllFunctions.t) (filename : string) : unit =
  let d_cfgedge chan dest src =
    Printf.fprintf chan "\t\t%i -> %i\n" (CFG.node_id src) (CFG.node_id dest) in
  let d_cfgnode chan (cfg : CFG.graph) (n : CFG.node) (nd : statement) =
    Printf.fprintf chan 
      "\t\t%i [label=\"%i: %s\"]\n" 
      (CFG.node_id n)
      (CFG.node_id n) 
      (String.escaped (Pulp_Syntax_Print.string_of_statement nd));    
      List.iter (fun dest -> d_cfgedge chan dest n) (CFG.succ cfg n) in
  
  AllFunctions.iter 
    (fun name cfg -> 
      let chan = open_out (filename ^ "." ^ name ^ ".cfg.dot") in
      Printf.fprintf chan "digraph iCFG {\n\tnode [shape=box,  labeljust=l]\n";
      Printf.fprintf chan "\tsubgraph \"cluster_%s\" {\n\t\tlabel=\"%s\"\n" name (String.escaped name);
      List.iter (fun n -> d_cfgnode chan cfg n (CFG.get_node_data cfg n)) (CFG.nodes cfg);
      Printf.fprintf chan  "\t}\n";
      Printf.fprintf chan "}\n";
      close_out chan
    ) 
    cfgs
 
let mk_cfg prog file = 
  let cfg = program_to_cfg prog in
  print_cfg cfg file;
  cfg
  
  