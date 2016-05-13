open SSyntax
open Set

let get_proc_variables proc = 
	
	let var_table = Hashtbl.create 1021 in 
	
	let rec loop cmd_list vars = 
		match cmd_list with 
		| [] -> vars 
		| cmd :: rest_cmds -> 
			(match cmd with 
			| SBasic (SAssignment (var, expr)) ->
				if (not (Hashtbl.mem var_table var)) 
					then
						(Hashtbl.add var_table var true;  
						loop cmd_list (var :: vars))
					else loop rest_cmds vars 
			| _ -> loop rest_cmds vars) in 
	
	loop proc.proc_body [] 			


let derelativize_gotos_proc proc =
	let rec derelative_gotos_cmds cmd_list cmd_number new_cmds =  
		match cmd_list with
		| [] -> List.rev new_cmds 
		| cmd :: rest_cmds -> 
			(match cmd with 
			| SGoto i -> 
				derelative_gotos_cmds 
					rest_cmds 
					(cmd_number + 1)
					((SGoto (i + cmd_number)) :: new_cmds)
			| SGuardedGoto (e, i, j) ->
				derelative_gotos_cmds 
					rest_cmds 
					(cmd_number + 1)
					((SGuardedGoto (e, (i + cmd_number), (j + cmd_number))) :: new_cmds)
			| x -> 
				derelative_gotos_cmds 
					rest_cmds 
					(cmd_number + 1)
					( cmd :: new_cmds)) in 
	
	let new_cmds = derelative_gotos_cmds proc.proc_body 0 [] in
	let new_proc = { proc with proc_body = new_cmds } in 
	new_proc

let derelativize_gotos prog = 
	SSyntax.SProgram.iter 
	(fun proc_name proc ->
		let new_proc = derelativize_gotos_proc proc in 
		SSyntax.SProgram.add prog proc_name new_proc)
	prog		

let get_proc_nodes cmd_list = 	
	let number_of_cmds = List.length cmd_list in 
	let cmd_arr = Array.make number_of_cmds (SSyntax.SBasic SSyntax.SSkip) in 
	
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
	let succ_table, pred_table = SSyntax_Utils_Graphs.get_succ_pred proc.proc_body in 
	(*  get an array of nodes instead of a list *)
	let nodes = get_proc_nodes proc.proc_body in 
	(* perform a dfs on the graph *) 
	let tree_table, parent_table, _, _, dfs_num_table_f, dfs_num_table_r = SSyntax_Utils_Graphs.dfs succ_table in 
	(* get the variables defined in proc *)
	let vars = get_proc_variables proc in 
	nodes, vars, succ_table, pred_table, tree_table, parent_table, dfs_num_table_f, dfs_num_table_r
		
	 