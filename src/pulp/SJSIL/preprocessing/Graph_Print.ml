let dot_of_graph succ_table nodes string_of_node graphname = 
	
	let number_of_nodes = Array.length succ_table in 
	
	(**
		return: 0[shape=box, label=cmd_0]; ...;n[shape=box, label=cmd_n];  
	*)
	let rec dot_of_graph_nodes_iter cur_node cur_str = 
		(if (cur_node < number_of_nodes)
			then 
				let node_str = (string_of_node nodes.(cur_node) cur_node) in 
				let cur_str = cur_str ^ "\t" ^ (string_of_int cur_node) ^ "[shape=box, label=\"" ^ node_str ^ "\"];\n" in 
					dot_of_graph_nodes_iter (cur_node+1) cur_str
			else 
				cur_str) in
	
	(**
    node_i -> node_j; where j \in succ(i)
  *)
	let rec dot_of_graph_edges_iter cur_node cur_edges cur_str = 
		(match cur_edges with 
		| [] -> 
				(if ((cur_node + 1) < number_of_nodes)
					then 
						let cur_node = cur_node + 1 in 
						let cur_edges = succ_table.(cur_node) in 
							dot_of_graph_edges_iter cur_node cur_edges cur_str 
					else 
						cur_str)
		| node :: rest_edges ->
				let cur_node_str = (string_of_int cur_node) in
				let node_str = (string_of_int node) in 
				let cur_str = cur_str ^ "\t" ^ cur_node_str ^ " -> " ^ node_str ^ ";\n" in
					Printf.printf "adding the edge (%s, %s) to the cfg\n" cur_node_str node_str; 
					dot_of_graph_edges_iter cur_node rest_edges cur_str) in 
	
	let str = "digraph " ^ graphname ^ "{\n" in 
	let str_nodes = dot_of_graph_nodes_iter 0 "" in 
	let str_edges = dot_of_graph_edges_iter 0 succ_table.(0) "" in 
	Printf.printf "I finish printing the edges\n";  
	let str = str ^ str_nodes ^ str_edges ^ "}" in
		str



let dot_of_tree parent_table nodes string_of_node graphname = 
	
	let number_of_nodes = Array.length parent_table in 
	
	(**
		return: 0[shape=box, label=cmd_0]; ...;n[shape=box, label=cmd_n];  
	*)
	let rec dot_of_tree_nodes_iter cur_node cur_str = 
		(if (cur_node < number_of_nodes)
			then 
				let node_str = (string_of_node nodes.(cur_node)) in 
				let cur_str = cur_str ^ "\t" ^ (string_of_int cur_node) ^ "[shape=box, label=\"" ^ node_str ^ "\"];\n" in 
					dot_of_tree_nodes_iter (cur_node+1) cur_str
			else 
				cur_str) in
	
	(**
    node_i -> node_j; where parent(node_j) = node_i
  *)
	let rec dot_of_tree_edges_iter cur_node cur_str = 
		(if (cur_node < number_of_nodes)
			then 
				let cur_node_str = string_of_int cur_node in
				let p_cur_node = parent_table.(cur_node) in 
				let cur_str = 
					(match p_cur_node with 
						| Some p_cur_node -> 
								let p_cur_node_str = string_of_int p_cur_node in 
									cur_str ^ "\t" ^ p_cur_node_str ^ " -> " ^ cur_node_str ^ ";\n"
						| None -> cur_str) in 
				dot_of_tree_edges_iter (cur_node+1) cur_str
			else 
				cur_str) in
	
	let str = "digraph " ^ graphname ^ "{\n" in 
	let str_nodes = dot_of_tree_nodes_iter 0 "" in 
	let str_edges = dot_of_tree_edges_iter 0 "" in 
	Printf.printf "I finish printing the edges\n";  
	let str = str ^ str_nodes ^ str_edges ^ "}" in
		str
	
	
let print_node_table node_table print_node_content : string = 
	
	let number_of_nodes = Array.length node_table in 
	
	let rec loop cur_node_index cur_str = 
		if (cur_node_index < number_of_nodes) 
			then 
				let node_content_str = print_node_content node_table.(cur_node_index) in 
				let cur_str = cur_str ^ (string_of_int cur_node_index) ^ ": " ^ node_content_str ^ ";\n" in 
				loop (cur_node_index + 1) cur_str 
			else cur_str in 
	
	loop 0 ""

(* print list of integers *)
let print_int_list (i_list : int list) : string = 
	let rec print_int_list_iter lst = 
		match lst with
		| [] -> "" 
		| [ a ] -> string_of_int a
		| a :: rest_lst -> (string_of_int a) ^ ", " ^ (print_int_list_iter rest_lst) in 
	"[" ^ (print_int_list_iter i_list) ^ "]"


let string_of_which_pred which_pred = 	
	Hashtbl.fold
		(fun (u, v) i str ->
			"pred(" ^ (string_of_int u) ^ ", " ^ (string_of_int v) ^ ") = " ^ (string_of_int i) ^ "; " ^ str)
		which_pred
		""

	