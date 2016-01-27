open Graphs
open Pulp_Syntax
open Control_Flow
open Simp_Common

type state_graph_node = {
    sgn_id : CFG.node;
    sgn_state : Pulp_Logic.formula
  }
  
let mk_sg_node id s = {
    sgn_id = id;
    sgn_state = s
  }
  
let string_of_state_graph_node sgn cfg =
  Printf.sprintf "%s \n %s" 
  (Pulp_Logic_Print.string_of_formula sgn.sgn_state)
  (Pulp_Syntax_Print.string_of_statement (CFG.get_node_data cfg sgn.sgn_id))
  

module StateG = AbstractGraph (struct type t = state_graph_node end) (struct type t = unit end)
 
let print_state_graph (sg : StateG.graph) cfg (fname) (filename : string) : unit =
  let d_cfgedge chan dest src =
    let sgn_src = StateG.get_node_data sg src in
    let sgn_dest = StateG.get_node_data sg dest in
    let edge_data = CFG.get_edge_data cfg sgn_src.sgn_id sgn_dest.sgn_id in
    let edge = match edge_data with
      | Edge_Normal -> ""
      | Edge_Excep -> "excep"
      | Edge_True -> "true"
      | Edge_False -> "false"
    in
    Printf.fprintf chan "\t\t%i -> %i [label=\"%s\"] \n" (StateG.node_id src) (StateG.node_id dest) edge in
  let d_cfgnode chan (sg : StateG.graph) (n : StateG.node) (nd : state_graph_node) =
    Printf.fprintf chan 
      "\t\t%i [label=\"%i: %s\"]\n" 
      (StateG.node_id n)
      (StateG.node_id n) 
      (String.escaped (string_of_state_graph_node nd cfg));    
      List.iter (fun dest -> d_cfgedge chan dest n) (StateG.succ sg n) in
  
      let chan = open_out (filename ^ "." ^ fname ^ ".state_graph.dot") in
      Printf.fprintf chan "digraph iCFG {\n\tnode [shape=box,  labeljust=l]\n";
      Printf.fprintf chan "\tsubgraph \"cluster_%s\" {\n\t\tlabel=\"%s\"\n" fname (String.escaped fname);
      List.iter (fun n -> d_cfgnode chan sg n (StateG.get_node_data sg n)) (StateG.nodes sg);
      Printf.fprintf chan  "\t}\n";
      Printf.fprintf chan "}\n";
      close_out chan
    

