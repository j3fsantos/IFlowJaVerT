module AbstractGraph (NodeData : sig type t end) (EdgeData : sig type t end) :
sig 
   type graph 
   type node
  
   exception GraphException of string
   
   val node_id : node -> int
   val nodes : graph -> node list
   val succ : graph -> node -> node list
   val pred : graph -> node -> node list
   val eq : node -> node -> bool
    
   val mk_graph : unit -> graph
   val mk_node : graph -> NodeData.t -> node
   val rm_node : graph -> node -> unit
   
   val mk_edge : graph -> node -> node -> EdgeData.t -> unit
   val rm_edge : graph -> node -> node -> unit
  
   val get_node_data : graph -> node -> NodeData.t
   val get_edge_data : graph -> node -> node -> EdgeData.t

end 