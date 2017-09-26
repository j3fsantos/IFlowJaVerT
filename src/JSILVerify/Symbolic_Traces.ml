open JSIL_Syntax
open Symbolic_State


(* Creates a new symbolic execution graph node *)
let sg_node_init 
		(symb_state : symbolic_state)
		(node_type  : symb_graph_node_type) : symb_graph_node =
	
	JSIL_Print.escape_string := true; 
	let heap_str  = Symbolic_State_Print.string_of_symb_heap (ss_heap symb_state) in
	let store_str = Symbolic_State_Print.string_of_symb_store (ss_store symb_state) in
	let pfs_str   = Symbolic_State_Print.string_of_pfs (ss_pfs symb_state) in
	let gamma_str = Symbolic_State_Print.string_of_gamma (ss_gamma symb_state) in
	let preds_str = Symbolic_State_Print.string_of_preds (ss_preds symb_state) in
	JSIL_Print.escape_string := false; 

	{	(* state *)
		heap_str    = heap_str;
		store_str   = store_str;
		pfs_str     = pfs_str;
		gamma_str   = gamma_str;
		preds_str   = preds_str;
		(* cmd *)
		node_type   = node_type; 
		node_number = (-1) }

let sg_node_from_cmd 
		(symb_state  : symbolic_state) 
		(cmd_index   : int)
		(cmd         : jsil_cmd) : symb_graph_node = 

	JSIL_Print.escape_string := true; 
	let cmd_str = (JSIL_Print.string_of_cmd_aux "" cmd_index cmd) in 
	JSIL_Print.escape_string := false; 
	sg_node_init symb_state (SGCmdNode (cmd_str, cmd_index))

let sg_node_from_lcmd 
		(symb_state  : symbolic_state) 
		(lcmd         : jsil_logic_command) : symb_graph_node = 
	JSIL_Print.escape_string := true; 
	let lcmd_str = JSIL_Print.string_of_lcmd lcmd in 
	JSIL_Print.escape_string := false; 
	sg_node_init symb_state (SGLCmdNode lcmd_str)

let sg_node_from_post (symb_state  : symbolic_state) : symb_graph_node = 
	sg_node_init symb_state SGPostNode

let sg_node_from_pre (symb_state  : symbolic_state) : symb_graph_node = 
	let node_info = sg_node_init symb_state SGPreNode in 
	{ node_info with node_number = 0 }

let sg_node_from_err (msg : string) : symb_graph_node = 
	{	(* state *)
		heap_str    = "";
		store_str   = "";
		pfs_str     = "";
		gamma_str   = "";
		preds_str   = "";
		(* cmd *)
		node_type   = (SGErrorNode msg); 
		node_number = (-1) }

let string_of_sg_node_type (nt : symb_graph_node_type) : string = 
	match nt with 
	| SGCmdNode (cmd, index) -> Printf.sprintf "CMD %d: %s\n" index cmd 
	| SGLCmdNode lcmd        -> Printf.sprintf "LCMD: %s\n" lcmd 
	| SGPreNode              -> "Precondition\n"
	| SGPostNode             -> "Postcondition\n"
	| SGErrorNode msg        -> Printf.sprintf "ERROR: %s\n" msg


let string_of_sg_node (node : symb_graph_node) : string =

	let cmd_info_str  = string_of_sg_node_type node.node_type in
	let heap_str      = "HEAP: " ^ node.heap_str ^ "\n" in
	let store_str     = "STORE: " ^ node.store_str ^ "\n" in
	let pfs_str       = "PFs: " ^ node.pfs_str ^ "\n" in
	let gamma_str     = "TYPEs: " ^ node.gamma_str ^ "\n" in
	let preds_str     = "PREDs: " ^ node.preds_str ^ "\n" in
	let dashes        = "-----------------------------------------\n" in
	heap_str ^ store_str ^ pfs_str ^ gamma_str ^ preds_str ^ dashes ^ cmd_info_str 

let dot_of_symb_exec_ctxt 
		(sec : symbolic_execution_context) (proof_name : string) : string =
	
	(** Returns 0[shape=box, label=cmd_0]; ...;n[shape=box, label=cmd_n]; *)
	let dot_of_search_nodes (nodes : (int, symb_graph_node) Hashtbl.t) : string =
		Hashtbl.fold 
			(fun node_id node ac -> 
				let node_str = string_of_sg_node node in 
				ac ^ "\t" ^ (string_of_int node_id) ^ "[shape=box, label=\"" ^ node_str ^ "\"];\n")
			nodes "" in 

	(** Returns: node_i -> node_j; where j \in succ(i) *)
	let dot_of_edges (edges : (int, int list) Hashtbl.t) : string  =
		Hashtbl.fold 
			(fun node_id neighbours ac -> 
				let cur_arrows = List.map (fun n_id -> "\t" ^ (string_of_int node_id)  ^ " -> " ^ (string_of_int n_id) ^ ";") neighbours in 
				ac ^ (String.concat "\n" cur_arrows) ^ "\n")
			edges "" in 

	let str       = "digraph " ^ proof_name ^ "{\n" in
	let str_nodes = dot_of_search_nodes sec.info_nodes in
	let str_edges = dot_of_edges sec.info_edges in
	str ^ str_nodes ^ str_edges ^ "}" 
