open Graphs
open Pulp_Syntax
open Control_Flow

type state_graph_node = {
    sgn_id : CFG.node;
    sgn_state : Pulp_Logic.formula
  }
  
let mk_sg_node id s = {
    sgn_id = id;
    sgn_state = s
  }

module StateG = AbstractGraph (struct type t = state_graph_node end) (struct type t = unit end)

