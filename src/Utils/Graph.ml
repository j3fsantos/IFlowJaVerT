open Set
open JSIL_Syntax

(* node set *)
 module NS = Set.Make(
	struct
		let compare = Pervasives.compare
		type t = int
	end)

let graph_verbose = ref false

let get_succ_pred cmds opt_ret_label opt_error_label =

	let cmds = Array.map (fun x -> match x with (_, cmd) -> cmd) cmds in

	let ret_label =
		(match opt_ret_label with
		| None -> -1021
		| Some l -> l) in

	let err_label =
		(match opt_error_label with
		| None -> -1021
		| Some l -> l) in

	let number_of_cmds = Array.length cmds in
	let succ_table = Array.make number_of_cmds [] in
	let pred_table = Array.make number_of_cmds [] in

	(* adding i to the predecessors of j *)
	let update_pred_table i j =
		(if ((j < number_of_cmds) && (i < number_of_cmds))
			then pred_table.(j) <- i :: pred_table.(j)
			else ()) in

	(* adding i to the successors of j *)
	let update_succ_table i j =
		(if ((j < number_of_cmds) && (i < number_of_cmds))
			then succ_table.(j) <- i :: succ_table.(j)
			else ()) in

	for u=0 to number_of_cmds-1 do
			(match cmds.(u) with
			| SBasic _
			| SPhiAssignment (_, _)
			| SPsiAssignment (_, _) ->
				if (not ((u == ret_label) || (u == err_label)))
					then
					begin
						update_succ_table (u + 1) u;
						update_pred_table u (u + 1)
					end

			| SGoto i ->
				if (not ((u == ret_label) || (u == err_label)))
					then
					begin
						update_succ_table i u;
						update_pred_table u i
					end

			| SGuardedGoto (e, i, j) ->
				if (not ((u == ret_label) || (u == err_label)))
					then
					begin
						update_succ_table i u;
						update_pred_table u i;
						update_succ_table j u;
						update_pred_table u j
					end

			| SCall (_, _, _, i) ->
				(match i with
				| None -> ()
				| Some i -> (update_succ_table i u; update_pred_table u i));
				if (not ((u == ret_label) || (u == err_label)))
					then
					begin
						update_succ_table (u+1) u;
						update_pred_table u (u+1)
					end

			| SApply (_, _, i) ->
				(match i with
				| None -> ()
				| Some i -> (update_succ_table i u; update_pred_table u i));
				if (not ((u == ret_label) || (u == err_label)))
					then
					begin
						update_succ_table (u+1) u;
						update_pred_table u (u+1)
					end)
	done;

	for k = 0 to (number_of_cmds - 1) do
		succ_table.(k) <- List.rev succ_table.(k);
		pred_table.(k) <- List.rev pred_table.(k);
	done;
	succ_table, pred_table


let dfs (succ_table : ((int list) array)) =

	let clock = ref 0 in
	let cur_dfs_num = ref 0 in
	let number_of_nodes : int = Array.length succ_table in

	let visited_table : bool array = Array.make number_of_nodes false in
	let parents_table : int option array = Array.make number_of_nodes None in
	let tree_table : int list array = Array.make number_of_nodes [] in
	let pre_table : int array = Array.make number_of_nodes (-1) in
	let post_table : int array = Array.make number_of_nodes (-1) in
	let dfs_num_table_r : int array = Array.make number_of_nodes (-1) in
	let dfs_num_table_f : int array = Array.make number_of_nodes (-1) in

	let pre_visit i =
		let clock_val = !clock in
		let dfs_num = !cur_dfs_num in
		pre_table.(i) <- clock_val;
		dfs_num_table_r.(dfs_num) <- i;
		dfs_num_table_f.(i) <- dfs_num;
		clock := clock_val + 1;
		cur_dfs_num := dfs_num + 1 in

	let post_visit i =
		let clock_val = !clock in
		post_table.(i) <- clock_val;
		clock := clock_val + 1 in

	let rec search i =
		pre_visit i;
		visited_table.(i) <- true;
		let i_successors = succ_table.(i) in
		List.iter
			(fun j ->
				if (not (visited_table.(j)))
				then
					(tree_table.(i) <- (j::(tree_table.(i)));
					parents_table.(j) <- (Some i);
					search j)
				else ())
			i_successors;
		post_visit i in

	search 0;
	tree_table, parents_table, pre_table, post_table, dfs_num_table_f, dfs_num_table_r

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

(*
	1. Do a simple dfs
	2. Check which nodes haven't been visited
	3. Remove these nodes
	4. Recompute labels and successors
*)

let very_simple_dfs (succ_table : ((int list) array)) =

	let number_of_nodes : int = Array.length succ_table in
	let visited_table : bool array = Array.make number_of_nodes false in

	let rec search i =
		visited_table.(i) <- true;
		let i_successors = succ_table.(i) in
		List.iter
			(fun j ->
				if (not (visited_table.(j)))
				then
					search j
				else ())
			i_successors; in

	search 0;

	(if (!graph_verbose)
		then
			(Printf.printf "\t Visited nodes: ";
			for i = 0 to (number_of_nodes -1) do
				Printf.printf "%b " (visited_table.(i));
			done;
			Printf.printf "\n")
		else ());

	visited_table



(* Removing unreachable code *)
let remove_unreachable_code proc throw =

	(if (!graph_verbose) then Printf.printf "Removing unreachable code.\n" else ());

	let cmds = proc.proc_body in
		let lret = proc.ret_label in
			let lerr = proc.error_label in
				let succ_table, pred_table = get_succ_pred cmds lret lerr in
					let visited = very_simple_dfs succ_table in
						let length : int = Array.length visited in
							let lnum_shift = Array.make length 0 in
								let shift = ref 0 in
									for i = 0 to (length - 1) do
										if (not visited.(i))
											then (if (not throw) then (shift := !shift + 1) else (raise (Failure "Unreachable code detected.")))
											else ();
										lnum_shift.(i) <- i - !shift;
										(if (!graph_verbose)
											then Printf.printf "\t i = %d; lsh = %d; shift = %d : %s\n" i lnum_shift.(i) !shift (JSIL_Print.string_of_cmd 0 0 cmds.(i))
											else ())
									done;

  (match lret with
	| None -> () (* (Printf.printf "\t WARNING: Return label does not exist!\n") *)
	| Some lret -> if (not visited.(lret))
									then ()); (* (Printf.printf "\t WARNING: Return label is unreachable and will be removed, along with the corresponding specs!\n")); *)


	(match lerr with
	| None -> () (* (Printf.printf "\t WARNING: Error label does not exist!\n") *)
	| Some lerr -> if (not visited.(lerr))
									then ()); (* (Printf.printf "\t WARNING: Error label is unreachable and will be removed, along with the corresponding specs!\n")); *)

	(if (!graph_verbose) then Printf.printf "\t Adjusting line numbers. \n" else ());

	let lret =
		(match lret with
		  | None -> None
			| Some lret -> if (not visited.(lret)) then None else (Some lret)) in

	let lerr =
		(match lerr with
		  | None -> None
			| Some lerr -> if (not visited.(lerr)) then None else (Some lerr)) in

	(* Adjust line numbers *)
	for u = 0 to (length - 1) do
		let spec, cmd = cmds.(u) in
		match cmd with
		| SGoto i ->
				cmds.(u) <- (spec, SGoto (lnum_shift.(i)))
		| SGuardedGoto (e, i, j) ->
				cmds.(u) <- (spec, SGuardedGoto (e, (lnum_shift.(i)), (lnum_shift.(j))))
		| SCall (v, e, le, i) ->
				cmds.(u) <- (spec, SCall (v, e, le, match i with | None -> None | Some i -> Some (lnum_shift.(i))))
		| _ -> ()
	done;

	(if (!graph_verbose) then Printf.printf "\t Removing unvisited commands. \n" else ());

	(* Remove unvisited commands *)
	let new_length = length - !shift in
		let new_cmds = Array.make new_length (empty_metadata, SBasic SSkip) in
			let shift = ref 0 in
				for i = 0 to (length - 1) do
					if (visited.(i))
							then (new_cmds.(i - !shift) <- cmds.(i))
							else (shift := !shift + 1)
				done;

	(if (!graph_verbose) then Printf.printf "\t Returning adjusted procedure. \n" else ());

	let new_spec =
	let lspec = proc.spec in
		(match lspec with
		| None -> None
		| Some lspec -> Some
    {
  		spec_name = lspec.spec_name;
      spec_params = lspec.spec_params;
      previously_normalised = false;
  		proc_specs =
  			let specs = lspec.proc_specs in
  			(match lerr with
  				| Some _ -> specs
  				| None -> let rec loop lspec =
  									(match lspec with
  									| [] -> []
  									| spec :: lspec ->
  											if (spec.ret_flag = Error)
  												then (loop lspec)
  												else (spec :: loop lspec)) in
                            loop specs)

		}) in

	(* Return adjusted procedure *)
	{
    proc_name   = proc.proc_name;
    proc_body   = new_cmds;
   	proc_params = proc.proc_params;
		ret_label   = (match lret with
		                | None -> None
										| Some lret -> Some lnum_shift.(lret));
		ret_var     = (match lret with
		                | None -> None
										| _ -> proc.ret_var);
		error_label = (match lerr with
		                | None -> None
										| Some lerr -> Some lnum_shift.(lerr));
		error_var   = (match lerr with
		                | None -> None
										| _ -> proc.error_var);
		spec        = new_spec;
	}



let compute_dominators pred succ =

	let rec range_iter i j cur_ns =
		if (i > j)
		then cur_ns
		else
			(if (i = j)
			then NS.add i cur_ns
			else range_iter (i+1) j (NS.add i cur_ns)) in

	let number_of_nodes = Array.length succ in
	let all_nodes = range_iter 0 (number_of_nodes - 1)  NS.empty in
	let dom_table =  Array.make (number_of_nodes) all_nodes in
	dom_table.(0) <- NS.singleton 0;

	let rec compute_dom_intersection lst cur_intersection =
		match lst with
		| [] -> cur_intersection
		| i :: rest_lst ->
			let new_cur_intersection = NS.inter cur_intersection dom_table.(i) in
			compute_dom_intersection rest_lst new_cur_intersection in

	let rec add_successors work_list nodes =
		match nodes with
		| [] -> work_list
		| node :: rest_nodes ->
			if (List.mem node work_list)
				then add_successors work_list rest_nodes
				else add_successors (work_list @ [ node ]) rest_nodes in

	let rec compute_dominators_iter work_list =
		match work_list with
		| [] -> ()
		| i :: rest_work_list ->
			let doms_i = compute_dom_intersection (pred.(i)) all_nodes in
			let doms_i = NS.add i doms_i in
			if (not (NS.equal doms_i  dom_table.(i) ))
				then
					(dom_table.(i) <- doms_i;
					let rest_work_list = add_successors rest_work_list succ.(i) in
					compute_dominators_iter rest_work_list)
				else
					compute_dominators_iter rest_work_list in

	compute_dominators_iter [ 0 ];
	dom_table


(**
  Compute the reachability table using the warshall algorithm
*)

module ReachGraph = Hashtbl.Make(
	struct
		type t = int * int
		let equal = (=)
		let hash = Hashtbl.hash
	end)

let graph_insert graph i j = ReachGraph.add graph (j, i) true

let graph_check graph i j =
	try
		let _ = (ReachGraph.find graph (i, j)) in
		true
	with _ -> false

let compute_reachability_graph succ_table =

	let number_of_nodes =  Array.length succ_table in
	let graph = ReachGraph.create 80021 in

	let rec init_reach_graph_iter cur_node_number cur_succs =
		match cur_succs with
		| [] ->
			let next_node_number = cur_node_number + 1 in
			if (next_node_number < number_of_nodes)
			then init_reach_graph_iter next_node_number succ_table.(next_node_number)
			else ()
		| i :: rest_succs ->
			graph_insert graph cur_node_number i;
			init_reach_graph_iter cur_node_number rest_succs in

	let warshall_algorithm () =
		let upper_limit = (number_of_nodes - 1)  in
		for k = 0 to upper_limit do
			for i = 0 to upper_limit do
				for j = 0 to upper_limit do
					if (graph_check graph i j)
					then ()
					else
						(if ((graph_check graph i k) && (graph_check graph k j))
						then  graph_insert graph i j
						else ())
				done
			done
		done	in

	init_reach_graph_iter 0 succ_table.(0);
	warshall_algorithm ();
	graph


(**
  Compute dominators using the Lengauer and Tarjan algorithm
*)


(**
 Link/Eval functions
 *)
let init_link_eval number_of_nodes =

	let ancestor = Array.make (number_of_nodes) None in
	let label = Array.make (number_of_nodes) 0 in

  (* start by initiating the labels *)
	for k = 0 to (number_of_nodes-1) do
	  label.(k) <- k
	done;

	let rec compress v semi_table =
		match ancestor.(v) with
		| Some u ->
			(match ancestor.(u) with
			| Some _ ->
				compress u semi_table;
				(if (semi_table.(label.(u)) < semi_table.(label.(v)) )
					then label.(v) <- label.(u)
					else ());
				(match ancestor.(u) with
					| Some w ->
						ancestor.(v) <- Some w
					| _ -> ())
			| _ -> ())
		| _ -> () in

	let link (v : int) (w : int) : unit =
		ancestor.(w) <- Some v in

	let eval (v : int) (semi_table : int array) : int =
		(if (ancestor.(v) = None)
			then v
			else
				(compress v semi_table;
				label.(v))) in

	(* return link/eval functions *)
	link, eval


(**
 * GIVEN
 * succ(v): the set of vertices such that (v, w) is an edge of the graph
 * pred(w): the set of vertices v such that (v, w) is an edge of the graph
 * parent(w): the vertex which is the parent of w in the spanning tree generated by the dfs
 * dfs(v): the dfs-entry visiting number
 *
 * COMPUTED
 * semi(w):
     - after step 1 semi(w) is dfs_num(w)
		 - after step 2 semi(w) is the semidominator of w
 * bucket(w):
     - after step 1 bucket(w) is the empty list
		 - after step 2 bucket(w) is the set of vertices whose semidominator is w
 * dom(w):
 *   - after step 2, if the semidominator of w is its immediate dominator, then dom(w)
       is the immediate dominator of w. Otherwise, dom(w) is a vertex v whose dfs-number is
			 smaller than the dfs number of w and whose immediate dominator is also w's immediate
			 domminator
     - afet step 3, dom(w) is the immediate dominator of w.
 *
 * STEPS
 * Step 1 - compute the semidominators of all vertices by applying theorem 4 of the paper.
            the computation is carried out vertex by vertex in decreasing order
 * Step 2 - implicitly define the immediate dominator of each vertex by applying corollary 1.
 * Step 3 - explicitly define the immediate dominator of each vertex, carrying out the
            computation vertex by vertex in increasing dfs order.
 **)

let lt_dom_algorithm succ_table pred_table (parent : int option array) (dfs_num_f : int array) (dfs_num_r : int array) =

	let number_of_nodes = Array.length succ_table in

	(* outputs *)
	let semi_dom : int array = Array.make number_of_nodes 0 in
	let bucket : int list array = Array.make number_of_nodes [] in
	let dom : int array = Array.make number_of_nodes 0 in
	let rev_dom : int list array = Array.make number_of_nodes [] in
	let link, eval = init_link_eval number_of_nodes in

	(* Step 1 *)
	for k = 0 to (number_of_nodes - 1) do
		semi_dom.(k) <- k;
	done;

	(* Step 2 *)
	for k = 1 to number_of_nodes do
		let cur_node = dfs_num_r.(number_of_nodes - k) in
		(if (!graph_verbose) then Printf.printf "Starting to process node number %s!!!\n" (string_of_int cur_node) else ());
		let p_cur_node =  parent.(cur_node) in
		let p_cur_node_str = match  parent.(cur_node) with
		| None -> "none"
		| Some p_cur_node -> (string_of_int p_cur_node) in
		(if (!graph_verbose) then Printf.printf "\tParent: %s!!!\n" p_cur_node_str else ());
	  let cur_node_predecessors = pred_table.(cur_node) in
		List.iter
			(fun pred ->
				let u = eval pred semi_dom in
				(if (!graph_verbose) then Printf.printf "\tPred: %s,  eval: %s!!!\n" (string_of_int pred) (string_of_int u) else ());
				(if (!graph_verbose)
					then
						Printf.printf "\t %s %s %s %s \n"
							(string_of_int (semi_dom.(u)))
							(string_of_int (semi_dom.(cur_node)))
							(string_of_int (dfs_num_f.(semi_dom.(u))))
							(string_of_int (dfs_num_f.(semi_dom.(cur_node))))
					else ());
				(if (dfs_num_f.(semi_dom.(u)) < dfs_num_f.(semi_dom.(cur_node)))
					then
						(semi_dom.(cur_node) <- semi_dom.(u);
						(if (!graph_verbose) then
							Printf.printf "\tUpdated Semi! Semi(%s) = %s\n"
								(string_of_int cur_node)
								(string_of_int semi_dom.(cur_node))
							else ()))
					else ()))
			cur_node_predecessors;

		(* add cur_node to the bucket of semi_dominator(cur_node) *)
		bucket.(semi_dom.(cur_node)) <- cur_node :: bucket.(semi_dom.(cur_node));

		(* link parent(cur_node) to cur_node *)
		(match p_cur_node with
		| Some p_cur_node ->
			link p_cur_node cur_node;
			List.iter
				(fun v ->
					let u = (eval v semi_dom) in
					dom.(v) <- (if ((dfs_num_f.(semi_dom.(u))) < (dfs_num_f.(semi_dom.(v)))) then u else p_cur_node))
				bucket.(p_cur_node);
			bucket.(p_cur_node) <- []
		| None -> ());
	done;

	let semis_str = Graph_Print.print_node_table semi_dom string_of_int in
	(if (!graph_verbose) then Printf.printf "Urray, I computed the semis:\n %s" semis_str else ());

	(* Step 3 *)
	for k = 1 to (number_of_nodes-1) do
		let cur_node = dfs_num_r.(k) in
		let d_cur_node = dom.(cur_node) in
		if (d_cur_node != semi_dom.(cur_node))
			then
				let dd_cur_node = dom.(dom.(cur_node)) in
					dom.(cur_node) <- dd_cur_node;
					rev_dom.(dd_cur_node) <- cur_node :: rev_dom.(dd_cur_node)
			else
					rev_dom.(d_cur_node) <- cur_node :: rev_dom.(d_cur_node)
	done;

	dom.(0) <- 0;
	dom, rev_dom


(* simple dfs *)
let simple_dfs succ =

	let number_of_nodes = Array.length succ in
	let visited : bool array = Array.make number_of_nodes false in
	let order : int Queue.t = Queue.create () in

	let rec search i =
		visited.(i) <- true;
		let i_successors = succ.(i) in
		List.iter
			(fun j ->
				if (not (visited.(j)))
				then
					(Queue.add j order;
					search j)
				else ())
			i_successors in

	search 0;
	Queue.fold
		(fun ac elem -> elem :: ac)
		[]
		order


(**
	* Computing Dominance Frontiers using the algorithm by Cytron et al
	* Inputs
	* succ: successors
	* idom_tree: the immediate dominators tree - predecessor (which is a single one)
	* idom_graph: the graph version - successors
	*)
let find_dominance_frontiers succ idom_table idom_graph =

	let number_of_nodes = Array.length succ in
	let dom_rev_order = simple_dfs idom_graph in
	let dominance_frontiers = Array.make number_of_nodes [] in

	let dom_rev_order_str = Graph_Print.print_int_list dom_rev_order in
	(if (!graph_verbose) then Printf.printf "DOM Rev Order:\n%s\n\n" dom_rev_order_str else ());

	let rec fdf_iter nodes_to_visit =
		(match nodes_to_visit with
		| [] -> ()
		| u :: rest_nodes_to_visit ->
			let u_successors = succ.(u) in
			List.iter
				(fun v ->
					(if (!graph_verbose)
						then
							Printf.printf "iteration of the dominance frontier algorithm. u: %s, v: %s, idom(v): %s\n"
								(string_of_int u)
								(string_of_int v)
								(string_of_int idom_table.(v))
						else ());
					if (idom_table.(v) != u)
						then
							dominance_frontiers.(u) <- (v :: dominance_frontiers.(u))
						else ())
				u_successors;
			let u_children = idom_graph.(u) in
			List.iter
				(fun v ->
					List.iter
						(fun w ->
							if (idom_table.(w) != u)
								then dominance_frontiers.(u) <- (w :: dominance_frontiers.(u))
								else ()
						)
						dominance_frontiers.(v)
				)
				u_children;
			fdf_iter rest_nodes_to_visit) in

	fdf_iter dom_rev_order;
	dominance_frontiers