open Lexing
(* open Core.Std *)
open SSyntax_Utils_Graphs
open SSyntax_SSA

let file = ref ""

let arguments () =
  let usage_msg="Usage: -file <path>" in
  Arg.parse
    [ 
			"-file", Arg.String(fun f -> file := f), "file to run";
      (* *)
    ]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg

let burn_to_disk path data = 
	let oc = open_out path in 
		output_string oc data; 
		close_out oc 

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try SJSIL_Parser.prog_target SJSIL_Lexer.read lexbuf with
  | SJSIL_Lexer.SyntaxError msg ->
    Printf.fprintf stderr "%a: %s\n" print_position lexbuf msg;
		[]
  | SJSIL_Parser.Error ->
    Printf.fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)

let rec parse_and_print lexbuf =
	Printf.printf "parse and print\n"; 
  match parse_with_error lexbuf with
  | proc :: lst ->
		let str_proc = SSyntax_Print.sexpr_of_procedure proc false in 
		Printf.printf "Parsing Successful! %s" str_proc;
		(* *)
		let proc = SSyntax_Utils.derelativize_gotos_proc proc in
		let succ_table, pred_table = get_succ_pred proc.proc_body in 
		let nodes = SSyntax_Utils.get_proc_nodes proc.proc_body in 
		let cur_string_of_cmd cmd =  SSyntax_Print.string_of_cmd cmd 0 0 false true in 
		let tree_table, parent_table, _, _, dfs_num_table_f, dfs_num_table_r = SSyntax_Utils_Graphs.dfs succ_table in 
		Printf.printf "\nI am going to compute the dominators!!!\n\n";
		let str_dfs_nums = Graph_Print.print_node_table dfs_num_table_f string_of_int in 
		Printf.printf "DFS nums:\n %s" str_dfs_nums; 
		let dom_table, rev_dom_table = SSyntax_Utils_Graphs.lt_dom_algorithm succ_table pred_table parent_table dfs_num_table_f dfs_num_table_r in
		let dominance_frontiers = SSyntax_Utils_Graphs.find_dominance_frontiers succ_table dom_table rev_dom_table in 
		let str_domfrontiers = Graph_Print.print_node_table dominance_frontiers Graph_Print.print_int_list in
		Printf.printf "Dominance frontiers:\n %s" str_domfrontiers;
		(* *)
		let vars = SSyntax_Utils.get_proc_variables proc in 
		let number_of_nodes = Array.length succ_table in
		let phi_functions_per_node = SSyntax_SSA.insert_phi_functions proc.proc_body dominance_frontiers number_of_nodes in 
		let phi_functions_per_node_str : string = SSyntax_SSA.print_phi_functions_per_node phi_functions_per_node in 
		Printf.printf "\n\n!!!!Phi Functions Per node!!!!!\n\n %s" phi_functions_per_node_str; 
		let phi_functions_per_node = SSyntax_SSA.insert_phi_args 
			succ_table pred_table dom_table rev_dom_table phi_functions_per_node proc.proc_params vars nodes in
		let new_proc_body = SSyntax_SSA.insert_phi_nodes phi_functions_per_node nodes in 
		let new_succ_table, new_pred_table = get_succ_pred new_proc_body in  
		let new_nodes = SSyntax_Utils.get_proc_nodes new_proc_body in   
		let proc_graph_str = Graph_Print.dot_of_graph new_succ_table new_nodes cur_string_of_cmd proc.proc_name in
		let dom_graph_str = Graph_Print.dot_of_graph rev_dom_table nodes cur_string_of_cmd proc.proc_name in
		(* Printf.printf "\n\n!!!!we are here!!!!!\n\n %s" phi_functions_per_node_str; *)
		(* let tree_graph_str = Graph_Print.dot_of_graph tree_table nodes cur_string_of_cmd proc.proc_name in *)
		burn_to_disk "ssa_graph.dot" proc_graph_str;
		burn_to_disk "dom_graph.dot" dom_graph_str;
    parse_and_print lexbuf
		
  | [] -> 
		Printf.printf "Empty Procedure List..."; 
		()


let parse_with_error_logic lexbuf =
  try JSIL_Logic_Parser.main_target JSIL_Logic_Lexer.read lexbuf with
  | JSIL_Logic_Lexer.SyntaxError msg ->
    Printf.fprintf stderr "Lexer Error at position %a: %s\n" print_position lexbuf msg;
		[]
  | JSIL_Logic_Parser.Error ->
    Printf.fprintf stderr "Syntax Error at position %a\n" print_position lexbuf;
    exit (-1)

let parse_and_print_logic lexbuf = 
	Printf.printf "parse and print\n";
	let rec print_logic spec_list =
    match spec_list with
    | spec :: rest ->
  		Printf.printf "%s\n\n\n" (JSIL_Logic_Print.string_of_spec spec);
			print_logic rest
  	| [] -> 
  		Printf.printf "Spec List Completed..."; 
  		()
	in
	print_logic (parse_with_error_logic lexbuf)

let process_file filename =
	Printf.printf "loop...\n"; 
	(* let inx = In_channel.create filename in *)
	let inx = open_in filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_and_print lexbuf;
  close_in inx

let main () = 
	arguments ();
	Printf.printf "Start parsing! %s\n" !file;
	process_file !file 


let _ = main()