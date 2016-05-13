open Lexing
(* open Core.Std *)
open SSyntax
open SSyntax_Utils_Graphs

let file = ref ""
let show_init_graph = ref false
let show_dfs = ref false 
let show_dom = ref false 
let show_dom_frontiers = ref false 
let show_phi_placement = ref false
let show_ssa = ref false 

let arguments () =
  let usage_msg="Usage: -file <path>" in
  Arg.parse
    [ 
			(* file to compile *)
			"-file", Arg.String(fun f -> file := f), "file to run";
			(* print ssa *)
			"-ssa", Arg.Unit(fun () -> show_ssa := true), "print ssa graph";
			(* print dfs *)
			"-dfs", Arg.Unit(fun () -> show_dfs := true), "print dfs graph";
      (* print dominators *)
			"-dom", Arg.Unit(fun () -> show_dom := true), "print dominator graph";
			(* print dominance frontiers *)
			"-frontiers", Arg.Unit(fun () -> show_dom_frontiers := true), "print dominance frontiers";
			(* print phi placement *)
			"-phis", Arg.Unit(fun () -> show_phi_placement := true), "print phi nodes placement";
			(* print init graph *)
			"-init", Arg.Unit(fun () -> show_init_graph := true), "print initial graph";			
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

let cond_print_graph test graph nodes string_of_node graph_name proc_folder = 
	if (test) 
		then 
			(let graph_str = Graph_Print.dot_of_graph graph nodes string_of_node graph_name in
			burn_to_disk (proc_folder ^ "/" ^ graph_name ^ ".dot") graph_str)
		else () 	

let pre_process_proc output_folder_name proc = 
	
	(* computing everything *)
	let proc = SSyntax_Utils.derelativize_gotos_proc proc in
	let nodes, vars, succ_table, pred_table, tree_table, parent_table, dfs_num_table_f, dfs_num_table_r = 
		SSyntax_Utils.get_proc_info proc in 
	let rev_dom_table, dominance_frontiers, phi_functions_per_node, new_proc = 
		SSyntax_SSA.ssa_compile proc vars nodes succ_table pred_table parent_table dfs_num_table_f dfs_num_table_r in 
	let final_succ_table, final_pred_table = SSyntax_Utils_Graphs.get_succ_pred new_proc.proc_body in 
	let new_nodes = SSyntax_Utils.get_proc_nodes new_proc.proc_body in   
	
	(* Printing everything *) 
	let proc_folder = (output_folder_name ^ "/" ^ proc.proc_name) in 
	Utils.safe_mkdir proc_folder; 
	let string_of_cmd cmd i =
		let str_i = string_of_int dfs_num_table_f.(i) in  
		str_i ^ ": " ^ SSyntax_Print.string_of_cmd cmd 0 0 false true in
	let string_of_cmd_ssa cmd i =  
		SSyntax_Print.string_of_cmd cmd 0 0 false true in

	cond_print_graph (!show_init_graph) succ_table nodes string_of_cmd "succ" proc_folder;	
	cond_print_graph (!show_dfs) tree_table nodes string_of_cmd "dfs" proc_folder;	
	cond_print_graph (!show_dom) rev_dom_table nodes string_of_cmd "dom" proc_folder;
	cond_print_graph (!show_ssa) final_succ_table new_nodes string_of_cmd_ssa "ssa" proc_folder;
	
	(if (!show_dom_frontiers) 
		then 
			let str_domfrontiers = Graph_Print.print_node_table dominance_frontiers Graph_Print.print_int_list in
			burn_to_disk (proc_folder ^ "/dom_frontiers.txt") str_domfrontiers
		else ()); 
	
	(if (!show_phi_placement) 
		then 
			let phi_functions_per_node_str : string = SSyntax_SSA.print_phi_functions_per_node phi_functions_per_node in 
			burn_to_disk (proc_folder ^ "/phi_placement.txt") phi_functions_per_node_str
		else ()); 
	new_proc
		
let rec parse_and_print lexbuf =
	let output_folder_name = Filename.chop_extension !file in 
  let proc_list = parse_with_error lexbuf in 
	Utils.safe_mkdir output_folder_name;
	let ssa_proc_list = List.map  (fun proc -> (pre_process_proc output_folder_name proc)) proc_list in 
	ssa_proc_list 

let parse_with_error_logic lexbuf =
  try JSIL_Logic_Parser.main_target JSIL_Logic_Lexer.read lexbuf with
  | JSIL_Logic_Lexer.SyntaxError msg ->
    Printf.fprintf stderr "Lexer Error at position %a: %s\n" print_position lexbuf msg;
		[]
  | JSIL_Logic_Parser.Error ->
    Printf.fprintf stderr "Syntax Error at position %a\n" print_position lexbuf;
    exit (-1)

let parse_and_print_logic lexbuf = 
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
	(* let inx = In_channel.create filename in *)
	let inx = open_in filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_and_print lexbuf;
  close_in inx

let main () = 
	arguments ();
	(* Printf.printf "Start parsing! %s\n" !file; *)
	process_file !file 

let _ = main()