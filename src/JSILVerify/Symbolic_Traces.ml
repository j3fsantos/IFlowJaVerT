open JSIL_Syntax
open Symbolic_State

(* Registering a new node (adding it to the search info) *)
(* Returns the search info after adding the new node *)
let register_new_node
    (search_info : symbolic_execution_search_info)
    (node : search_info_node) : symbolic_execution_search_info =

  (* Increment the node counter *)
  let curr_node_number = !(search_info.next_node) in
  search_info.next_node := curr_node_number + 1;

  (* Add the node to the nodes table *)
  Hashtbl.add (search_info.info_nodes) curr_node_number node;

  (* Update the edges *)
  Hashtbl.replace search_info.info_edges node.node_number [];
  let parent_node_info = search_info.cur_node_info in
  let parent_children  = Hashtbl.find search_info.info_edges parent_node_info.node_number in
  Hashtbl.replace search_info.info_edges parent_node_info.node_number ((node.node_number) :: parent_children);
  search_info

(* Creates a new node *)
let create_new_info_node
    (symb_state : symbolic_state option)
    (some_cmd_index : int option)
	(node_number : int)
	(label : node_label) : search_info_node =

	let cmd_index =
	    match some_cmd_index with
	    | Some i -> i
	    | None -> (-1)
	in
	{
		symb_state = symb_state;
		cmd_index  = cmd_index;
		label      = label;
		node_number = node_number
	}

(* Adds a new node to the graph *)
let add_new_info_node
	(symb_state : symbolic_state option)
	(some_cmd_index : int option)
	(search_info : symbolic_execution_search_info)
	(label : node_label) : symbolic_execution_search_info =

  	let new_node : search_info_node = create_new_info_node symb_state some_cmd_index !(search_info.next_node) label in
  	register_new_node search_info new_node  

(* Adding a node from an l-cmd *)
let add_info_node_from_lcmd
    (search_info : symbolic_execution_search_info)
    (symb_state : symbolic_state)
    (lcmd : jsil_logic_command) : symbolic_execution_search_info =

	add_new_info_node (Some symb_state) None search_info (LCmd lcmd)

(* Adding a node from a cmd *)
let add_info_node_from_cmd
    (search_info : symbolic_execution_search_info)
    (symb_state : symbolic_state)
    (cmd : jsil_cmd)
    (cmd_index : int) : symbolic_execution_search_info =

	add_new_info_node (Some symb_state) (Some cmd_index) search_info (Cmd cmd)

(* Adding a node from an invariant *)
let add_info_node_from_invariant
	(search_info : symbolic_execution_search_info)
	(symb_state : symbolic_state)
	(is_post : bool) : symbolic_execution_search_info =
	
	(* TODO: investigate this message? *)
	let msg = if (is_post) then "Postcondition" else "Invariant" in
	add_new_info_node (Some symb_state) None search_info (Msg msg)

(* Adding a node from a post-condition *)
let add_info_node_from_post
	(search_info : symbolic_execution_search_info)
	(symb_state : symbolic_state)
	(ret_flag : jsil_return_flag) : symbolic_execution_search_info =

	let msg = ("Postcondition. Ret flag: " ^
		(match ret_flag with
		| Normal -> "NORMAL"
		| Error -> "ERROR")) in

	add_new_info_node (Some symb_state) None search_info (Msg msg)

(* Error nodes *)
let add_info_node_from_error
	(search_info : symbolic_execution_search_info)
	(error_msg : string) : symbolic_execution_search_info =

    let msg = "ERROR: " ^ (String.escaped error_msg) in
    add_new_info_node None None search_info (Msg msg)