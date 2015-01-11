open Graphs
open Pulp_Syntax

let entry = "Entry"

type edge_type =
  | Edge_Normal
  | Edge_Excep
  | Edge_True
  | Edge_False

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
  
let connect_calls_throw g throwl node = 
  let stmt = CFG.get_node_data g node in
  match stmt with
    | Basic (Assignment {assign_right = (Call _)}) -> 
      CFG.mk_edge g node throwl Edge_Excep
    | _ -> ()
  
  
let rec connect_nodes g current nodes label_map = 
  let stmt = CFG.get_node_data g current in
  match stmt with
    | Goto l -> 
      let lnode = Hashtbl.find label_map l in
      CFG.mk_edge g current lnode Edge_Normal
    | GuardedGoto (_, l1, l2) ->
      let lnode1 = Hashtbl.find label_map l1 in
      CFG.mk_edge g current lnode1 Edge_True;
      let lnode2 = Hashtbl.find label_map l2 in
      CFG.mk_edge g current lnode2 Edge_False
    | _ -> 
      begin match nodes with
        | [] -> ()
        | hd :: tail -> 
          CFG.mk_edge g current hd Edge_Normal;
          connect_nodes g hd tail label_map
     end

let mk_cfg fb : CFG.graph = 
  let g = CFG.mk_graph () in
  
  let start = CFG.mk_node g (Label entry) in
  
  let nodes = List.map (CFG.mk_node g) 
    (fb.func_body) in
    
  let throwl = CFG.mk_node g (Label fb.func_ctx.label_throw) in  
  let _ = CFG.mk_node g (Label fb.func_ctx.label_return) in 
 
  let label_map = get_all_labels g in
  connect_nodes g start nodes label_map;
  
  List.iter (connect_calls_throw g throwl) nodes;
  g
  
  