open CCommon
open JSIL_Syntax
open Symbolic_State


(* Creates a new symbolic execution graph node *)
let sg_node_init 
		(symb_state : symbolic_state)
		(node_type  : symb_graph_node_type) : symb_graph_node =
	{	
		symb_state  = Some symb_state; 
		node_type   = node_type; 
		node_number = (-1) 
	}

let sg_node_from_cmd 
		(symb_state  : symbolic_state) 
		(cmd_index   : int)
		(cmd         : jsil_cmd) : symb_graph_node = 
	sg_node_init symb_state (SGCmdNode (cmd, cmd_index))

let sg_node_from_lcmd 
		(symb_state   : symbolic_state) 
		(lcmd         : jsil_logic_command) : symb_graph_node = 
	sg_node_init symb_state (SGLCmdNode lcmd)

let sg_node_from_post (symb_state  : symbolic_state) : symb_graph_node = 
	sg_node_init symb_state SGPostNode

let sg_node_from_pre (symb_state  : symbolic_state) : symb_graph_node = 
	let node_info = sg_node_init symb_state SGPreNode in 
	{ node_info with node_number = 0 }

let sg_node_from_err (msg : string) : symb_graph_node = 
	{	
		symb_state  = None; 
		node_type   = (SGErrorNode msg); 
		node_number = (-1) }

let string_of_sg_node_type (nt : symb_graph_node_type) (js_lines : (string array * (int, int) Hashtbl.t) option) : string = 
	CCommon.escape_string := true; 
	Symbolic_State_Print.escape_string := true; 
	let str = 
		(match nt, js_lines with 
		| SGCmdNode (cmd, index), None          -> Printf.sprintf "CMD %d: %s\n" index (JSIL_Print.string_of_cmd_aux "" index cmd) 
		| SGCmdNode (cmd, index), Some (js_lines, line_mapper)  -> 
			Printf.sprintf "CMD %d: %s\n" index (js_lines.((Hashtbl.find line_mapper index) - 1))
		| SGLCmdNode lcmd, _                    -> Printf.sprintf "LCMD: %s\n" (JSIL_Print.string_of_lcmd lcmd)
		| SGPreNode, _                          -> "Precondition\n"
		| SGPostNode, _                         -> "Postcondition\n"
		| SGErrorNode msg, _                    -> Printf.sprintf "ERROR: %s\n" msg) in
	CCommon.escape_string := false; 
	Symbolic_State_Print.escape_string := false; 
	str


let filter_symb_graph 
		(proc_name         : string)
		(proof_name        : string)
		(symb_graph        : symbolic_graph) 
		(symb_graph_filter : (string * int, int * bool) Hashtbl.t) : symbolic_graph = 


	let is_node_to_keep node = 
		(match node.node_type with 
		| SGCmdNode (cmd_str, cmd_index) ->  
			let _, b = Hashtbl.find symb_graph_filter (proc_name, cmd_index) in 
			b && (cmd_index <> 0)
		| SGLCmdNode (Fold (LPred (pname, _))) 
		| SGLCmdNode (Unfold (LPred (pname, _), _)) -> pname <> JS2JSIL_Constants.pi_predicate_name 
		| SGLCmdNode (Assert _)      
		| SGLCmdNode (ApplyLem _)   -> true
		| SGLCmdNode _              -> false 
		| _                         -> true) in 
	
	let get_node_from_id id = 
		try Hashtbl.find symb_graph.info_nodes id 
			with Not_found -> 
				(let msg = Printf.sprintf "DEATH. get_node_from_id %d" id in
				raise (Failure msg)) in 

	let new_sg = symb_graph_init symb_graph.root in 
	let nodes_to_visit = Queue.create () in 
	let is_visited     = Hashtbl.create medium_tbl_size in 

	let rec search prev_kept_node node = 
		if (Hashtbl.mem is_visited node.node_number) then () else (
			Hashtbl.replace is_visited node.node_number true; 
			let neighbours = try Hashtbl.find symb_graph.info_edges node.node_number 
				with Not_found -> raise (Failure "DEATH. filter_symb_graph. search. neighbours") in 
			let neighbours = List.map get_node_from_id neighbours in 
			if (not (is_node_to_keep node)) then (
				List.iter (search prev_kept_node) neighbours
			) else (
				Hashtbl.replace new_sg.info_nodes node.node_number node; 
				Hashtbl.replace new_sg.info_edges node.node_number []; 
				(match prev_kept_node with 
				| Some prev_kept_node -> 
					let prev_kept_neighbours = Hashtbl.find new_sg.info_edges prev_kept_node.node_number in 
					Hashtbl.replace new_sg.info_edges prev_kept_node.node_number (node.node_number :: prev_kept_neighbours)
				| None -> ()); 
				List.iter (search (Some node)) neighbours
			)
		) in 

	search None (symb_graph.root); 
	new_sg


let string_of_sg_node (node : symb_graph_node) (js_lines : (string array * (int, int) Hashtbl.t) option) : string =
	let cmd_info_str   = string_of_sg_node_type node.node_type js_lines in
	CCommon.escape_string := true; 
	Symbolic_State_Print.escape_string := true; 
	let symb_state_str = Option.map_default Symbolic_State_Print.string_of_symb_state "" node.symb_state in 
	let dashes         = "-----------------------------------------\n" in
	CCommon.escape_string := false; 
	Symbolic_State_Print.escape_string := false; 
	symb_state_str ^ dashes ^ cmd_info_str 


let dot_of_symb_graph 
		(graph_name : string) 
		(symb_graph : symbolic_graph) 
		(js_lines   : (string array * (int, int) Hashtbl.t) option) : string = 
	(** Returns 0[shape=box, label=cmd_0]; ...;n[shape=box, label=cmd_n]; *)
	let dot_of_search_nodes (nodes : (int, symb_graph_node) Hashtbl.t) : string =
		Hashtbl.fold 
			(fun node_id node ac -> 
				let node_str = string_of_sg_node node js_lines in 
				ac ^ "\t" ^ (string_of_int node_id) ^ "[shape=box, label=\"" ^ node_str ^ "\"];\n")
			nodes "" in 

	(** Returns: node_i -> node_j; where j \in succ(i) *)
	let dot_of_edges (edges : (int, int list) Hashtbl.t) : string  =
		Hashtbl.fold 
			(fun node_id neighbours ac -> 
				let cur_arrows = List.map (fun n_id -> "\t" ^ (string_of_int node_id)  ^ " -> " ^ (string_of_int n_id) ^ ";") neighbours in 
				ac ^ (String.concat "\n" cur_arrows) ^ "\n")
			edges "" in 

	let str       = "digraph " ^ graph_name ^ "{\n" in
	let str_nodes = dot_of_search_nodes symb_graph.info_nodes in
	let str_edges = dot_of_edges symb_graph.info_edges in
	str ^ str_nodes ^ str_edges ^ "}" 



let dot_of_symb_exec_ctxt 
		(sec               : symbolic_execution_context) 
		(proof_name        : string) 
		(symb_graph_filter : ((string * int, int * bool) Hashtbl.t * string array) option) : string * (string option)=
	
	let dot_graph     = dot_of_symb_graph proof_name sec.symb_graph None in 
	let dot_graph_js  = 
		(match symb_graph_filter with 
		| None -> None 
		| Some (symb_graph_filter, js_lines) -> 
			let line_mapper   = Hashtbl.create small_tbl_size in 
			Hashtbl.iter (fun (proc_name, i) (j, _) -> if (proc_name = sec.proc_name) then Hashtbl.replace line_mapper i j) symb_graph_filter; 
			let symb_graph_js = filter_symb_graph sec.proc_name proof_name sec.symb_graph symb_graph_filter in
			Some (dot_of_symb_graph (proof_name ^ "_js") symb_graph_js (Some (js_lines, line_mapper))))  in 
	dot_graph, dot_graph_js
