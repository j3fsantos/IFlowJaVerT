open SSyntax 

let get_assignments_per_var cmds  = 
	
	let assignments_per_var = Hashtbl.create 1021 in 
	let num_vars = ref 0 in 
	
	let rec get_assignments_per_var_iter cmds cur_cmd = 
		match cmds with 
		| [] -> ()
		| cmd :: rest_cmds ->
			(match cmd with 
			| SSyntax.SBasic (SSyntax.SAssignment (var, e)) ->
				let var_assignments = SSyntax_Aux.try_find assignments_per_var var in 
					(match var_assignments with 
					| None -> 
							num_vars := (!num_vars) + 1;
							Hashtbl.add assignments_per_var var [ cur_cmd ]
					| Some lst -> Hashtbl.replace assignments_per_var var (cur_cmd :: lst));
					get_assignments_per_var_iter rest_cmds (cur_cmd + 1)
			| _ -> get_assignments_per_var_iter rest_cmds (cur_cmd + 1)) in 
	
	get_assignments_per_var_iter cmds 0; 
	assignments_per_var, !num_vars
	
(** 
 Algorithm that finds where to insert the phi-nodes
 *)		
let get_phi_functions_per_var var (var_asses : int list) dom_frontiers phi_nodes_table number_of_nodes = 
	
	let work_list_flags : bool array = Array.make number_of_nodes false in
	let work_list = Stack.create () in 

	List.iter 
		(fun u ->  
			work_list_flags.(u) <- true; 
			Stack.push u work_list)
		var_asses;
	
	while (not (Stack.is_empty work_list)) do
		let u = Stack.pop work_list in 
			List.iter 
				(fun v -> 
					if (not (Hashtbl.mem phi_nodes_table (var, v)))
					then  
						(Hashtbl.add phi_nodes_table (var, v) true;  
						(if (not work_list_flags.(v)) 
							then 
								(work_list_flags.(v) <- true;
								Stack.push v work_list)
							else ()))
					else ())
			dom_frontiers.(u)
	done

let insert_phi_functions cmds dom_frontiers number_of_nodes = 
	
	let phi_nodes_table = Hashtbl.create 1021 in 
	let assignments_per_var, _ = get_assignments_per_var cmds in 
	let phi_functions_per_node = Array.make number_of_nodes [] in 
	
	Hashtbl.iter
		(fun var (var_ass_nodes : int list) -> 
			get_phi_functions_per_var var var_ass_nodes dom_frontiers phi_nodes_table number_of_nodes)
		assignments_per_var; 
	
	Hashtbl.iter 
		(fun (var, u) b -> 
			phi_functions_per_node.(u) <- var :: phi_functions_per_node.(u))
		phi_nodes_table; 
		
	phi_functions_per_node
	
		
		
(** 
 *
 * SSA main algorithm: phi-nodes insertion algorithm 
 *)
let insert_phi_args succ idom_table idom_graph phi_functions_per_node = 
	
	let vars_counter = Hashtbl.create 1021 in 
	let vars_stack = Hashtbl.create 1021 in 
	
	let number_of_nodes = Array.length succ in 
	let dom_rev_order = SSyntax_Utils_Graphs.simple_dfs idom_graph in 
	let dom_order = List.rev dom_rev_order in 
	
	let rec ipa_iter nodes_to_visit = 
		(match nodes_to_visit with 
		| [] -> () 
		| u :: rest_nodes_to_visit ->
			let u_successors = succ.(u) in
			()) in
	0

	
	
	
	
	
									 
			