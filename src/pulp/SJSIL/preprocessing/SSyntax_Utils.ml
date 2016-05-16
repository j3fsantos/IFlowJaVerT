open SSyntax
open Set

let get_proc_variables proc = 
	
	let var_table = Hashtbl.create 1021 in 
	let cmds = proc.proc_body in 
	let number_of_cmds = Array.length cmds in
	
	let rec loop u vars = 
		if (u >= number_of_cmds) 
			then vars 
			else 
				(match cmds.(u) with
				| SBasic (SAssignment (var, _)) 
				| SBasic (SLookup (var, _, _))
				| SBasic (SNew var) 
				| SBasic (SHasField (var, _, _))
				| SBasic (SProtoField (var, _, _))
				| SBasic (SProtoObj (var, _, _))
				| SCall (var, _, _, _) when (not (Hashtbl.mem var_table var)) ->	
						Hashtbl.add var_table var true;  
						loop (u+1) (var :: vars)
				| _ -> loop (u+1) vars) in 
	
	loop 0 [] 			


let derelativize_gotos_proc proc =
	
	let cmds = proc.proc_body in 
	let number_of_cmds = Array.length cmds in 
	
	for u=0 to (number_of_cmds-1) do 
		let cmd = cmds.(u) in 
		match cmd with 
		| SGoto i -> 
			cmds.(u) <- SGoto (i + u)
		| SGuardedGoto (e, i, j) ->
			cmds.(u) <- SGuardedGoto (e, (i + u), (j + u)) 
		| _ -> ()
	done
	

let derelativize_gotos prog = 
	SSyntax.SProgram.iter 
	(fun proc_name proc -> derelativize_gotos_proc proc)
	prog		

let get_proc_nodes cmd_list = 	
	let number_of_cmds = List.length cmd_list in 
	let cmd_arr = Array.make number_of_cmds (SBasic SSkip) in 
	
	let rec get_nodes_iter cmd_lst cur_node = 
		match cmd_lst with 
		| [] -> () 
		| cmd :: rest -> 
			cmd_arr.(cur_node) <- cmd; 
			get_nodes_iter rest (cur_node + 1) in 
	
	get_nodes_iter cmd_list 0; 
	cmd_arr

let get_proc_info proc = 
	(*  computing successors and predecessors *)
	let succ_table, pred_table = SSyntax_Utils_Graphs.get_succ_pred proc.proc_body proc.ret_label proc.error_label in 
	(* compute which_pred table *)
	let which_pred = SSyntax_Utils_Graphs.compute_which_preds pred_table in  
	(*  get an array of nodes instead of a list *)
	let nodes = proc.proc_body in 
	(* perform a dfs on the graph *) 
	let tree_table, parent_table, _, _, dfs_num_table_f, dfs_num_table_r = SSyntax_Utils_Graphs.dfs succ_table in 
	(* get the variables defined in proc *)
	let vars = get_proc_variables proc in 
	nodes, vars, succ_table, pred_table, tree_table, parent_table, dfs_num_table_f, dfs_num_table_r, which_pred
		
	 