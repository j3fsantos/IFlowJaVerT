open SSyntax 

let get_assignments_per_var cmds  = 
	
	let assignments_per_var = Hashtbl.create 1021 in 
	let num_vars = ref 0 in 
	let number_of_cmds = Array.length cmds in 
	
	for i=0 to number_of_cmds-1 do 
		let cmd = cmds.(i) in 
		match cmd with 
			| SBasic (SAssignment (var, _)) 
			| SBasic (SLookup (var, _, _))
			| SBasic (SNew var) 
			| SBasic (SHasField (var, _, _))
			| SBasic (SProtoField (var, _, _))
			| SBasic (SProtoObj (var, _, _))
			| SCall (var, _, _, _) ->	
				let var_assignments = SSyntax_Aux.try_find assignments_per_var var in 
					(match var_assignments with 
					| None -> 
							num_vars := (!num_vars) + 1;
							Hashtbl.add assignments_per_var var [ i ]
					| Some lst -> Hashtbl.replace assignments_per_var var (i :: lst))
			| _ -> ()
	done;		
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

let insert_phi_functions nodes dom_frontiers number_of_nodes = 
	
	let phi_nodes_table = Hashtbl.create 1021 in 
	let assignments_per_var, _ = get_assignments_per_var nodes in 
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
let rec rewrite_expr_ssa (expr : jsil_expr) var_stacks rename_var  = 
	match expr with 
	|	Literal l -> Literal l 
	| Var var -> 
		let var_stack = SSyntax_Aux.try_find var_stacks var in 
		(match var_stack with 
		| Some (i :: lst) -> Var (rename_var var i)
		| _ -> raise (Failure ("Variable " ^ (Printf.sprintf("%s") var) ^ " not found in stack table during ssa transformation")))
 	| BinOp (e1, binop, e2) ->
		let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in 
		let new_e2 = rewrite_expr_ssa e2 var_stacks rename_var in 
		BinOp (new_e1, binop, new_e2)
	| UnaryOp (un_op, e1) -> 
		let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in 
		UnaryOp (un_op, new_e1) 
	| VRef (e1, e2) -> 
		let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in 
		let new_e2 = rewrite_expr_ssa e2 var_stacks rename_var in 
		VRef (new_e1, new_e2) 
	| ORef (e1, e2) -> 
		let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in 
		let new_e2 = rewrite_expr_ssa e2 var_stacks rename_var in 
		ORef (new_e1, new_e2)  
 	| Base e1 -> 
		let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in
		Base (new_e1)
	| Field e1 -> 
		let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in
		Field (new_e1)
	| TypeOf e1 -> 
		let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in
		TypeOf (new_e1)


let rewrite_non_assignment_ssa cmd var_stacks rename_var = 
	match cmd with 
	| SBasic (SSkip) -> SBasic (SSkip) 
	| SBasic (SMutation (e1, e2, e3)) ->
			let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in 
			let new_e2 = rewrite_expr_ssa e2 var_stacks rename_var in
			let new_e3 = rewrite_expr_ssa e3 var_stacks rename_var in
			SBasic (SMutation (new_e1, new_e2, new_e3))
	| SBasic (SDelete (e1, e2)) ->
	 		let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in 
			let new_e2 = rewrite_expr_ssa e2 var_stacks rename_var in
			SBasic (SDelete (new_e1, new_e2))
	| SGoto j -> SGoto j
	| SGuardedGoto (e, i, j) -> 
		let new_e = rewrite_expr_ssa e var_stacks rename_var in 
		SGuardedGoto (new_e, i, j) 
	| _ ->
		let cmd_str = (SSyntax_Print.string_of_cmd cmd 0 0 false false) in  
		raise (Failure ("Cannot Rewrite the command " ^ cmd_str ^ " using in the non-assignment case of SSA Rewriting"))

let compute_which_preds pred = 
	let which_pred = Hashtbl.create 1021 in
	let number_of_nodes = Array.length pred in
	
	for u=0 to number_of_nodes-1 do 
		let cur_preds = pred.(u) in 
		List.iteri
			(fun i v -> 
				Hashtbl.add which_pred (v, u) i)
			cur_preds
	done; 
	
	which_pred
	
let print_which_pred which_pred = 	
	Hashtbl.fold
		(fun (u, v) i str ->
			"pred(" ^ (string_of_int u) ^ ", " ^ (string_of_int v) ^ ") = " ^ (string_of_int i) ^ "; " ^ str)
		which_pred
		""

let rename_var = fun (var : string) (i : int) -> var ^ "_" ^ (string_of_int i) 

let rename_params params = 
	let rec loop params new_params = 
		match params with 
		| [] -> new_params 
		| param :: rest_params -> 
			let new_param = rename_var param 0 in 
			loop rest_params (new_param :: new_params) in 
	loop params [] 

let print_phi_functions_per_node phi_functions_per_node = 
		
	let number_of_nodes = Array.length phi_functions_per_node in 
	let str = "Phi-functions per node: \n" in 
	
	let rec loop u cur_str =  
		if u >= number_of_nodes 
			then cur_str
			else 
				let phi_functions_for_u = phi_functions_per_node.(u) in 
				let str_u = (match phi_functions_for_u with 
					| [] -> "" 
					| [ v ] -> v
					| v :: rest_phi_functions ->  
							List.fold_left (fun acc x -> acc ^ ", " ^ x) v rest_phi_functions) in 
				let str_u = Printf.sprintf "%d must have phi-nodes for: %s\n" u str_u in 
				loop (u+1) (cur_str ^ str_u) in 
	
	loop 0 str

let insert_phi_args args vars cmds succ pred idom_table idom_graph phi_functions_per_node  = 
	
	let var_counters : (string, int) Hashtbl.t  = Hashtbl.create 1021 in 
	let var_stacks :  (string, int list) Hashtbl.t = Hashtbl.create 1021 in 
	let which_pred = compute_which_preds pred in 
	
	let number_of_nodes = Array.length succ in
	let new_cmds = Array.make number_of_nodes (SBasic SSkip) in 
	let new_phi_functions_per_node = Array.make number_of_nodes [] in 
	
	(* Printf.printf "Computed which pred %s\n " which_pred_str;	*)
	
	List.iter 
		(fun var -> 
			Hashtbl.add var_counters var 0;
			Hashtbl.add var_stacks var [])
		vars;
	
	List.iter 
		(fun var -> 
			Hashtbl.add var_counters var 1;
			Hashtbl.add var_stacks var [ 0 ])
		args;
	
	for u = 0 to number_of_nodes - 1 do
		let u_number_of_pred = (List.length pred.(u)) in 
		let u_phi_functions = phi_functions_per_node.(u) in 
		let new_u_phi_functions = 
			(List.map 
				(fun v -> v, (Array.make u_number_of_pred (-1)), v)
		 		u_phi_functions) in 
		new_phi_functions_per_node.(u) <- new_u_phi_functions
	done; 

	let rec ipa_rec u = 
 		let cmd = cmds.(u) in 
		
		let rec loop phi_nodes processed_phi_nodes = 
			match phi_nodes with 
			| [] -> 
				new_phi_functions_per_node.(u) <- processed_phi_nodes
			| (_, v_args, old_var) :: rest_phi_nodes -> 
				let var_index : int option = SSyntax_Aux.try_find var_counters old_var in
				let var_stack : int list option = SSyntax_Aux.try_find var_stacks old_var in 
				(match var_index, var_stack with 
 				| (Some index), (Some v_stack) ->
 					Hashtbl.replace var_counters old_var (index + 1);  
 					Hashtbl.replace var_stacks old_var (index :: v_stack);
					let new_var = rename_var old_var index in 
					loop rest_phi_nodes ((new_var, v_args, old_var) :: processed_phi_nodes)
 				| _ -> Printf.printf "Variable %s not found in stack table during ssa transformation - 1st phase - phi assignment.\n" old_var) in 
		
		let phi_nodes_for_u = new_phi_functions_per_node.(u) in 
		loop phi_nodes_for_u []; 
 		
		(* Printf.printf "Finished processing the lhs for the phi-nodes in %d!\n" u; *)
		
		let v_stack_and_counter_update var = 
			let var_index : int option = SSyntax_Aux.try_find var_counters var in
 			let var_stack : int list option = SSyntax_Aux.try_find var_stacks var in 
			Printf.printf "Processing an assignemnt to variable %s\n " var;
 			(match var_index, var_stack with 
 			| (Some index), (Some v_stack) ->
				let str_stack = 
					(match v_stack with 
					| [] -> "[]" 
					| [ v ] -> "[" ^ (string_of_int v) ^ "]"  
					| v :: rest_stack -> 
						(List.fold_left 
							(fun ac v -> ac ^ ", " ^ (string_of_int v)) 
							("[" ^ (string_of_int v))
							rest_stack) ^ "]") in 
				Printf.printf "\t Index: %d, Stack: %s\n " index str_stack;
 				Hashtbl.replace var_counters var (index + 1);  
 				Hashtbl.replace var_stacks var (index :: v_stack); 
				index
			| _ ->
				Printf.printf "Variable %s not found in stack table during ssa transformation - 1st phase - ordinary assignment.\n" var;  
				raise (Failure "Variable not found in stack table during ssa transformation")) in
		
 		let new_ass = (match cmd with 
 		| SBasic (SAssignment (var, expr)) -> 
 			let new_expr : jsil_expr = rewrite_expr_ssa expr var_stacks rename_var in
			let index = v_stack_and_counter_update var in
 			SBasic (SAssignment ((rename_var var index), new_expr)) 
			
 		| SBasic (SLookup (var, e1, e2)) ->
			let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in 
			let new_e2 = rewrite_expr_ssa e2 var_stacks rename_var in
			let index = v_stack_and_counter_update var in 
			SBasic (SLookup ((rename_var var index), new_e1, new_e2))
		
		| SBasic (SNew var) -> 
			let index = v_stack_and_counter_update var in 
			SBasic (SNew (rename_var var index)) 
		
		| SBasic (SHasField (var, e1, e2)) ->
			let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in 
			let new_e2 = rewrite_expr_ssa e2 var_stacks rename_var in
			let index = v_stack_and_counter_update var in
			SBasic (SHasField ((rename_var var index), new_e1, new_e2))	
			
		| SBasic (SProtoField (var, e1, e2)) ->
			let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in 
			let new_e2 = rewrite_expr_ssa e2 var_stacks rename_var in
			let index = v_stack_and_counter_update var in
			SBasic (SProtoField ((rename_var var index), new_e1, new_e2)) 
		
		| SBasic (SProtoObj (var, e1, e2)) ->
			let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in 
			let new_e2 = rewrite_expr_ssa e2 var_stacks rename_var in
			let index = v_stack_and_counter_update var in
			SBasic (SProtoObj ((rename_var var index), new_e1, new_e2)) 	
		
		| SCall (var, e, le, j) ->
			let new_e = rewrite_expr_ssa e var_stacks rename_var in 
			let new_le = List.map 
				(fun e -> rewrite_expr_ssa e var_stacks rename_var)
				le in 
			let index = v_stack_and_counter_update var in
			SCall((rename_var var index), new_e, new_le, j)  
		
		| cmd -> rewrite_non_assignment_ssa cmd var_stacks rename_var) in 
		new_cmds.(u) <- new_ass;
			
		(* Printf.printf "Finished processing the lhs for the node %d!\n" u; *)
		
 		let u_successors = succ.(u) in
 		List.iter 
 			(fun k -> 
 				let j = SSyntax_Aux.try_find which_pred (u, k) in
				match j with 
				| Some j -> 
					Printf.printf "%d is the %d^th predecessor of %d!\n" u k (j+1);
 					List.iter 
 				  	(fun (v, args, old_v) -> 
 							let v_stack = SSyntax_Aux.try_find var_stacks old_v in 
 							(match v_stack with 
 							| Some (i :: rest) -> 
 								args.(j) <- i  
 							| _ -> 
								Printf.printf "Variable %s not found in stack table during ssa transformation - 2nd phase.\n" old_v;  
								raise (Failure "Variable not found in stack table during ssa transformation"))
 						)
 						new_phi_functions_per_node.(k)
				| None -> 
					Printf.printf "%d is a predecessor of %d but I do not know which one.\n" u k;
					raise (Failure "Variable not found in stack table during ssa transformation"))
 			u_successors; 
 		
		(* Printf.printf "Finished processing the successors!\n"; *)
		
		List.iter 
			(fun v -> ipa_rec v)
			idom_graph.(u); 
		
		(match cmd with 
 		| SBasic (SAssignment (var, _)) 
		| SBasic (SLookup (var, _, _))
		| SBasic (SNew var) 
		| SBasic (SHasField (var, _, _))
		| SBasic (SProtoField (var, _, _))
		| SBasic (SProtoObj (var, _, _))
		| SCall (var, _, _, _) ->
			let var_stack = SSyntax_Aux.try_find var_stacks var in 
 			(match var_stack with 
 			| Some (hd :: rest_stack)  ->
 				Hashtbl.replace var_stacks var rest_stack; 
			| _ ->
				Printf.printf "Variable %s not found in stack table during ssa transformation.\n" var;   
				raise (Failure "Variable not found in stack table during ssa transformation"))
		| _ -> ()); 
		
		let rec loop phi_nodes = 
			match phi_nodes with 
			| [] -> ()
			| (var, v_args, old_var) :: rest_phi_nodes -> 
				let var_stack = SSyntax_Aux.try_find var_stacks old_var in 
 				(match var_stack with 
 				| Some (hd :: rest_stack)  ->
 					Hashtbl.replace var_stacks old_var rest_stack; 
				| _ ->
					Printf.printf "Variable %s has an empty stack...\n" old_var; 
					raise (Failure "Variable not found in stack table during ssa transformation"));
				loop rest_phi_nodes in
		
		let phi_nodes_for_u = new_phi_functions_per_node.(u) in 
		loop phi_nodes_for_u in 
			
	ipa_rec 0; 
	new_phi_functions_per_node, var_counters, new_cmds
 	
	
let create_phi_assignment var v_args old_var = 
	let len = Array.length v_args in 
	let new_v_args = Array.make len "" in 
	for i=0 to len-1 do 
		new_v_args.(i) <- (rename_var old_var v_args.(i))
	done; 
	SBasic (SPhiAssignment (var, new_v_args))

let adjust_goto cmd displacements = 
	match cmd with 
	| SGoto j -> SGoto (j + displacements.(j)) 
	| SGuardedGoto (e, i, j) -> SGuardedGoto (e, (i + displacements.(i)), (j + displacements.(j)))
	| x -> x 

let insert_phi_nodes proc phi_functions_per_node nodes var_counters = 
	
	let number_of_nodes : int = Array.length nodes in 
	let phi_assignments_per_node = Array.make	number_of_nodes [] in 
	let jump_displacements = Array.make number_of_nodes 0 in 
	
	let rec create_phi_assignments u phi_nodes_u n = 
		match phi_nodes_u with 
		| [] -> n
		| (var, v_args, old_var) :: rest_phi_nodes -> 
				let new_phi_assignment = create_phi_assignment var v_args old_var in 
				phi_assignments_per_node.(u) <- new_phi_assignment :: phi_assignments_per_node.(u); 
				create_phi_assignments u rest_phi_nodes (n + 1) in
	
	let ac_jump_displacement = ref 0 in 
	for u=0 to (number_of_nodes-1) do  
		jump_displacements.(u) <- (!ac_jump_displacement);
		Printf.printf ("Displacement of node %s: %s\n") (string_of_int u) (string_of_int (!ac_jump_displacement));
		let u_displacement = create_phi_assignments u phi_functions_per_node.(u) 0 in 
		ac_jump_displacement := u_displacement + (!ac_jump_displacement);
	done;
	
	let rec loop u processed_cmds = 
		if (u >= number_of_nodes) 
			then List.rev processed_cmds
			else 
				(let processed_cmd = adjust_goto nodes.(u) jump_displacements in 
				let new_processed_cmds : jsil_cmd list = List.append (phi_assignments_per_node.(u)) processed_cmds in 
				let new_processed_cmds : jsil_cmd list = processed_cmd :: new_processed_cmds  in 
				loop (u + 1) new_processed_cmds) in 
	
	let new_cmds = loop 0 [] in
	let new_cmds = SSyntax_Utils.get_proc_nodes new_cmds in  
	let new_params = List.map
		(fun param -> rename_var param 0)
		proc.proc_params in 
	
	let ret_label = proc.ret_label in 
	let new_ret_label = proc.ret_label + jump_displacements.(ret_label) + (List.length (phi_assignments_per_node.(ret_label))) in 
	let ret_var = proc.ret_var in 
	let ret_var_index = 
		(match SSyntax_Aux.try_find var_counters ret_var with 
		| None -> raise (Failure "Return variable index not found in SSA")
		| Some i -> i - 1) in  
	let new_ret_var = rename_var ret_var ret_var_index in 
	
	let error_label, error_var = proc.error_label, proc.error_var in
	let new_error_label, new_error_var = 
		(match error_label, error_var with
		 | None, None -> None, None
		 | Some lab, Some var -> Some (lab + jump_displacements.(lab) + (List.length (phi_assignments_per_node.(lab)))), Some var
		 | _, _ -> raise (Failure "Error variable and error label not both present or both absent!")) in
	let new_error_var = 
		(match new_error_var with
		  | None -> None
			| Some var -> 
					let error_var_index = 
						(match SSyntax_Aux.try_find var_counters var with 
						  | None -> raise (Failure "Error variable index not found in ssa")
							| Some i -> i - 1) in 
					let new_error_var = rename_var var error_var_index in
						Some new_error_var) in
	{ 
		proc_name = proc.proc_name; 
		proc_body = new_cmds; 
		proc_params = new_params; 
		ret_label = new_ret_label;
		ret_var = new_ret_var; 
		error_label = new_error_label; 
		error_var = new_error_var
	}
 

let ssa_compile proc (vars : string list) nodes succ_table pred_table parent_table dfs_num_table_f dfs_num_table_r = 
	let args : string list = proc.proc_params in 
	let number_of_nodes = Array.length succ_table in
  (* compute dominators using the Lengauer Tarjan Algorithm *)
	let dom_table, rev_dom_table = SSyntax_Utils_Graphs.lt_dom_algorithm succ_table pred_table parent_table dfs_num_table_f dfs_num_table_r in
	(* compute dominance frontiers using Cytron algorithm *) 
	let dominance_frontiers = SSyntax_Utils_Graphs.find_dominance_frontiers succ_table dom_table rev_dom_table in 
	(* compute which nodes need phi variables *)
	let phi_functions_per_node_init = insert_phi_functions nodes dominance_frontiers number_of_nodes in 
	(* compute the arguments of the phi nodes and rewrite all the nodes *)
	let phi_functions_per_node, var_counters, new_cmds = insert_phi_args 
			args vars nodes succ_table pred_table dom_table rev_dom_table phi_functions_per_node_init in
	(* insert the phi nodes in the program *)
	let new_proc = insert_phi_nodes proc phi_functions_per_node new_cmds var_counters in
	rev_dom_table, dominance_frontiers, phi_functions_per_node_init, new_proc

				