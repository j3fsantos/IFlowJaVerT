open Graphs
open Pulp_Syntax
open Simp_Common
open Control_Flow

module CFG_BB = AbstractGraph (struct type t = statement list end) (struct type t = edge_type end)

exception BBInvalid of string

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
  
let transform_to_basic_blocks (g : CFG_BB.graph) : CFG_BB.graph =
  let nodedone = Hashtbl.create 100 in
  match CFG_BB.nodes g with
    | [] -> g
    | start :: tail -> traverse_node g nodedone start;
  g
  
let remove_unreachable (g : CFG_BB.graph) : CFG_BB.graph =
  let nodedone = Hashtbl.create 100 in
  let rec traverse_graph current =
    if Hashtbl.mem nodedone current then ()
    else begin Hashtbl.add nodedone current (); List.iter traverse_graph (CFG_BB.succ g current) end
  in
    
  match CFG_BB.nodes g with
    | [] -> g
    | start :: tail -> traverse_graph start;
      
  List.iter (fun n -> if not (Hashtbl.mem nodedone n) then CFG_BB.rm_node g n) (CFG_BB.nodes g);
  g
  
  
let transform_to_basic_blocks_from_cfg (input : CFG.graph) : CFG_BB.graph =
  let g = copy input in
  transform_to_basic_blocks g
  
let rec filter_goto_label stmts throwl returnl =
  match stmts with
    | Goto l1 :: tail ->
      begin match tail with
        | Label l2 :: tail2 -> if (l1 = l2 && throwl <> l1 && returnl <> l1) then filter_goto_label tail2 throwl returnl
                               else [Goto l1; Label l2] @ filter_goto_label tail2 throwl returnl
        | _ -> Goto l1 :: filter_goto_label tail throwl returnl
      end
   | stmt :: tail -> stmt :: (filter_goto_label tail throwl returnl)
   | [] -> []
  
let remove_unnecessary_goto_label (g : CFG_BB.graph) throwl returnl =
  List.iter (fun n ->
    let stmts = CFG_BB.get_node_data g n in
    let filtered_stmts = filter_goto_label stmts throwl returnl in
    CFG_BB.set_node_data g n filtered_stmts
  ) (CFG_BB.nodes g)
  
let is_block_empty stmts =
  match stmts with
    | [Label l2; Goto l1] -> 
      true, l1, l2
    | _ -> false, "", ""
  
let remove_empty_blocks g =
  let change_if_equal l1 l2 tol =
    if l1 == l2 then tol else l1 in
  
  let change_last_goto stmts newl oldl = 
    let rev = List.rev stmts in
    match rev with
      | Goto l1 :: tail -> (List.rev tail) @ [Goto (change_if_equal l1 oldl newl)]
      | GuardedGoto (e, l1, l2) :: tail -> (List.rev tail) @ [GuardedGoto (e, (change_if_equal l1 oldl newl), (change_if_equal l2 oldl newl))]
      | _ -> raise (BBInvalid "Expected Goto in removing empty blocks") in
  
  List.iter (fun n ->
    let nd = CFG_BB.get_node_data g n in
    let is_empty, newl, oldl = is_block_empty nd in
    if is_empty then begin
      let succs = CFG_BB.succ g n in
      match succs with
        | [thesucc] -> 
           let preds = CFG_BB.pred g n in
           let sd = CFG_BB.get_edge_data g n thesucc in
           List.iter (fun pred -> 
             let stmts = CFG_BB.get_node_data g pred in
             let new_stmts = change_last_goto stmts newl oldl in
             CFG_BB.set_node_data g pred new_stmts;
             CFG_BB.mk_edge g pred thesucc sd
           ) preds;   
           CFG_BB.rm_node g n;
        | _ -> raise (BBInvalid "Goto should have excatly one successor")
	  end
    else ()
  ) (CFG_BB.nodes g)


let print_cfg_bb (cfgs : CFG_BB.graph AllFunctions.t) (filename : string) : unit =
  let cfg_index = ref 0 in
  let node_name n = 
    "c" ^ (string_of_int (!cfg_index)) ^ "n" ^ (string_of_int (CFG_BB.node_id n)) in
  let d_cfgedge chan dest src =
    Printf.fprintf chan "\t\t%s -> %s\n" (node_name src) (node_name dest) in
  let d_cfgnode chan (cfg : CFG_BB.graph) (n : CFG_BB.node) (nd : statement list) =
    Printf.fprintf chan 
      "\t\t%s [label=\"%s: %s\"]\n" 
      (node_name n)
      (node_name n)
      (String.escaped (Pulp_Syntax_Print.string_of_statement_list nd));    
      List.iter (fun dest -> d_cfgedge chan dest n) (CFG_BB.succ cfg n) in
  let chan = open_out (filename ^ ".cfg.dot") in
  Printf.fprintf chan "digraph iCFG {\n\tnode [shape=box,  labeljust=l]\n";
  AllFunctions.iter 
    (fun name cfg -> 
      cfg_index := !cfg_index + 1;
      Printf.fprintf chan "\tsubgraph \"cluster_%s\" {\n\t\tlabel=\"%s\"\n" name (String.escaped name);
      List.iter (fun n -> d_cfgnode chan cfg n (CFG_BB.get_node_data cfg n)) (CFG_BB.nodes cfg);
      Printf.fprintf chan  "\t}\n";
    ) 
    cfgs;
  Printf.fprintf chan "}\n";
  close_out chan
  
  
  

