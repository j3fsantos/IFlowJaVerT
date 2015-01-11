module AbstractGraph (NodeData : sig type t end) (EdgeData : sig type t end) =
struct 
  
   type node = int
  
   type graph = 
    {
      mutable graph_nodes : node list;    
      graph_succs : (node, node list) Hashtbl.t; 
      graph_preds : (node, node list) Hashtbl.t;
      graph_node_data : (node, NodeData.t) Hashtbl.t; 
      graph_edge_data : (node * node, EdgeData.t) Hashtbl.t;
      mutable graph_last_node : node;
    }
    
   exception GraphException of string
   
   let nodes g = g.graph_nodes
  
   let succ g n = 
    try Hashtbl.find g.graph_succs n
    with Not_found -> raise (GraphException ("Successor not found for node " ^ (string_of_int n)))
  
   let pred g n = 
    try Hashtbl.find g.graph_preds n
    with Not_found -> raise (GraphException ("Predecessor not found for node " ^ (string_of_int n)))
  
   let eq n1 n2 = n1 = n2
    
   let mk_graph () = 
   {
     graph_nodes = [];
     graph_succs = Hashtbl.create 100;
     graph_preds = Hashtbl.create 100;
     graph_node_data = Hashtbl.create 100;
     graph_edge_data = Hashtbl.create 100;
     graph_last_node = 0;
   }
    
   let mk_node g nd = 
     let n = g.graph_last_node + 1 in
     g.graph_last_node <- n;
     Hashtbl.add g.graph_succs n [];
     Hashtbl.add g.graph_preds n [];
     Hashtbl.add g.graph_node_data n nd;
     g.graph_nodes <- n :: g.graph_nodes;
     n
    
   let mk_edge g src dest ed = 
     if Hashtbl.mem g.graph_edge_data (src, dest)
     then raise (GraphException ("Duplicate edge " ^ (string_of_int src) ^ "-->" ^ (string_of_int dest)))
     else begin
	     Hashtbl.replace g.graph_succs src (dest :: (succ g src));
	     Hashtbl.replace g.graph_preds dest (src :: (pred g dest)); 
	     Hashtbl.add g.graph_edge_data (src, dest) ed
    end
    
   let rm_edge g src dest = 
     if not (Hashtbl.mem g.graph_edge_data (src, dest)) 
     then raise (GraphException ("Cannot remove non-existing edge " ^ (string_of_int src) ^ "-->" ^ (string_of_int dest)))
     else begin
	     Hashtbl.replace g.graph_succs src (List.filter (fun n -> n = dest) (succ g src));
	     Hashtbl.replace g.graph_preds dest (List.filter (fun n -> n = src) (pred g dest));
	     Hashtbl.remove g.graph_edge_data (src, dest)
     end
  
   let rm_node g n = 
     if not (Hashtbl.mem g.graph_node_data n) 
     then raise (GraphException ("Cannot remove non-existing node " ^ (string_of_int n)))
     else begin
	     let succs = succ g n in
	     let preds = pred g n in
	     List.iter (fun p -> rm_edge g p n) preds;
	     List.iter (fun s -> rm_edge g n s) succs;
	     Hashtbl.remove g.graph_succs n;
	     Hashtbl.remove g.graph_preds n;
	     Hashtbl.remove g.graph_node_data n;
	     g.graph_nodes <- (List.filter (fun rm -> n = rm) g.graph_nodes)
    end
  
   let get_node_data g n = 
     try Hashtbl.find g.graph_node_data n
     with Not_found -> raise (GraphException ("Data not found for node " ^ (string_of_int n)))
    
   let get_edge_data g src dest = 
     try Hashtbl.find g.graph_edge_data (src, dest)
     with Not_found -> raise (GraphException ("Data not found for edge " ^ (string_of_int src) ^ "-->" ^ (string_of_int dest)))

end