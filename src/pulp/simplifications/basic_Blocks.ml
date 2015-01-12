open Graphs
open Pulp_Syntax
open Simp_Common
open Control_Flow

module CFG_BB = AbstractGraph (struct type t = statement list end) (struct type t = edge_type end)

let copy (input : CFG.graph) : CFG_BB.graph = 
  let g = CFG_BB.mk_graph () in 
  
  let nodetbl = Hashtbl.create 100 in
  
  List.iter (fun n -> 
    let nd = CFG.get_node_data input n in
    let newn = CFG_BB.mk_node g [nd] in
    Hashtbl.add nodetbl n newn 
  ) (CFG.nodes input); 
  
  List.iter (fun n ->
    List.iter (
      fun dest ->
        let ed = CFG.get_edge_data input n dest in
        CFG_BB.mk_edge g (Hashtbl.find nodetbl n) (Hashtbl.find nodetbl dest) ed
    ) (CFG.succ input n)
  ) (CFG.nodes input);
  
  g
  
let merge_two_nodes n1 n2 g = 
  let n2data = CFG_BB.get_node_data g n2 in
  let n2succs = CFG_BB.succ g n2 in
  let n2succs_edges_data = List.map (fun n2succ -> (n2succ, CFG_BB.get_edge_data g n2 n2succ)) n2succs in
  CFG_BB.rm_node g n2;
  let n1data = CFG_BB.get_node_data g n1 in
  CFG_BB.set_node_data g n1 (n1data @ n2data);
  List.iter (fun (succ, data) ->
    CFG_BB.mk_edge g n1 succ data
  ) n2succs_edges_data
  

let rec traverse_node (g : CFG_BB.graph) nodedone current =
  if Hashtbl.mem nodedone current then () 
  else begin
	  let succs = CFG_BB.succ g current in
	  begin match succs with
	    | [succ] -> 
        let preds = CFG_BB.pred g succ in
        begin match preds with
          | [pred] -> merge_two_nodes current succ g; traverse_node g nodedone current 
          | _ -> Hashtbl.add nodedone current (); List.iter (traverse_node g nodedone) succs
        end;
	    | _ -> Hashtbl.add nodedone current (); List.iter (traverse_node g nodedone) succs
    end
  end
  
let transform_to_basic_blocks (input : CFG.graph) : CFG_BB.graph =
  let g = copy input in
  let nodedone = Hashtbl.create 100 in
  match CFG_BB.nodes g with
    | [] -> g
    | start :: tail -> traverse_node g nodedone start; g
  
  
  

