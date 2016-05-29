open Lexing
(* open Core.Std *)
open SSyntax
open SSyntax_Utils_Graphs
open SJSIL_Interpreter
open JSIL_Logic_Normalise

let file = ref ""
let specs = ref None 
let jsil_run = ref false
let show_init_graph = ref false
let show_dfs = ref false 
let show_dom = ref false 
let show_dom_frontiers = ref false 
let show_phi_placement = ref false
let show_ssa = ref false 

let do_ssa = ref false

let arguments () =
  let usage_msg="Usage: -file <path>" in
  Arg.parse
    [ 
			(* file to compile *)
			"-file", Arg.String(fun f -> file := f), "file to run";
			(* specs *)
			"-specs", Arg.String(fun f -> specs := (Some f)), "specs to check";
			(* run *)
			"-run", Arg.Unit(fun () -> jsil_run := true), "run the program given as input";
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

let string_of_cmd cmd i proc specs dfs_num_table_f =
	let str_i = string_of_int i in
	let str_dfs_i = string_of_int dfs_num_table_f.(i) in
		str_i ^ "/" ^ str_dfs_i ^ ": " ^ 
		(if (i = proc.ret_label) 
			then ("RET: ") 
			else 
				(match proc.error_label with
				| None -> ""
				| Some lab -> if (i = lab) then ("ERR: ") else (""))) ^ 
		SSyntax_Print.string_of_cmd cmd 0 0 false specs true 

let pre_process_proc output_folder_name proc = 
	
	(* computing everything *)

	(* Removing dead code and recalculating everything *)
	let proc = remove_unreachable_code proc false in
	let proc = remove_unreachable_code proc true in

	(* Proper pre-processing *) 
	Printf.printf "Starting proper pre-processing.\n";
	
	let proc_folder = (output_folder_name ^ "/" ^ proc.proc_name) in 
	Utils.safe_mkdir proc_folder; 
	
	let nodes, vars, succ_table, pred_table, tree_table, parent_table, dfs_num_table_f, dfs_num_table_r, which_pred = 
		SSyntax_Utils.get_proc_info proc in 
	let succ_table, pred_table = get_succ_pred proc.proc_body proc.ret_label proc.error_label in
	
	let string_of_cmd_ssa cmd i = SSyntax_Print.string_of_cmd cmd 0 0 false false true in 	
	let string_of_cmd_main cmd i = string_of_cmd cmd i proc true dfs_num_table_f in 
	
	cond_print_graph (!show_init_graph) succ_table nodes string_of_cmd_main "succ" proc_folder;	
	cond_print_graph (!show_dfs) tree_table nodes string_of_cmd_main "dfs" proc_folder;
	
	let dom_table, rev_dom_table = SSyntax_Utils_Graphs.lt_dom_algorithm succ_table pred_table parent_table dfs_num_table_f dfs_num_table_r in
	cond_print_graph (!show_dom) rev_dom_table nodes string_of_cmd_main "dom" proc_folder;
	
	if (!do_ssa) then
	begin
  	let rev_dom_table, dominance_frontiers, phi_functions_per_node, new_proc = 
  		SSyntax_SSA.ssa_compile proc vars nodes succ_table pred_table parent_table dfs_num_table_f dfs_num_table_r which_pred in 
  	let final_succ_table, final_pred_table = SSyntax_Utils_Graphs.get_succ_pred new_proc.proc_body new_proc.ret_label new_proc.error_label in   
  	
  	cond_print_graph (!show_ssa) final_succ_table new_proc.proc_body string_of_cmd_ssa "ssa" proc_folder;
  			
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
  	
  	let new_proc_str = SSyntax_Print.string_of_procedure new_proc false in 
  	Printf.printf "\n%s\n" new_proc_str; 
  
    (* returning proc and which_pred *)
  	new_proc, which_pred
	end
	else
	begin
		proc, which_pred
	end
		
let rec parse_and_preprocess_jsil_prog lexbuf =
	let output_folder_name = Filename.chop_extension !file in 
  let lproc_list = parse_with_error lexbuf in	
	let proc_list = SSyntax_Utils.desugar_labs_list lproc_list in
	let number_of_procs = List.length proc_list in 
	let prog = SProgram.create 1021 in 
	let global_which_pred = Hashtbl.create 1021 in 
	Utils.safe_mkdir output_folder_name;
	List.iter 
		(fun proc -> 
			let proc_name = proc.proc_name in 
			let processed_proc, which_pred = pre_process_proc output_folder_name proc in 
			SProgram.replace prog proc_name processed_proc; 
			(* Printf.printf "Just added the procedure %s to the program. It has %d params" proc_name (List.length processed_proc.proc_params);*)
			Hashtbl.iter 
				(fun (prev_cmd, cur_cmd) i ->
					Hashtbl.replace global_which_pred (proc_name, prev_cmd, cur_cmd) i)
				which_pred;
		) 
		proc_list; 
	prog, global_which_pred

let parse_with_error_logic lexbuf =
  try SJSIL_Parser.specs_target SJSIL_Lexer.read lexbuf with
  | SJSIL_Lexer.SyntaxError msg ->
    Printf.fprintf stderr "Lexer Error at position %a: %s\n" print_position lexbuf msg;
		[]
  | SJSIL_Parser.Error ->
    Printf.fprintf stderr "Syntax Error at position %a\n" print_position lexbuf;
    exit (-1)

let parse_and_print_logic lexbuf = 
	let spec_list = parse_with_error_logic lexbuf in
	let spec_table = Hashtbl.create 1021 in 
	List.iter
		(fun spec ->
			let spec_name = spec.spec_name in 
			let spec_params = spec.spec_params in 
			let pre_post_list = spec.proc_specs in 
			let normalized_pre_post_list = 
				List.map 
					(fun single_spec -> 
						let pre = single_spec.pre in 
						let post = single_spec.post in 
						let ret_flag = single_spec.ret_flag in 
						Printf.printf "About to normalize the beautiful assertion: %s \n" (JSIL_Logic_Print.string_of_logic_assertion pre false);
						let pre_heap, pre_store, pre_p_formulae = JSIL_Logic_Normalise.normalize_assertion_top_level pre in 
						Printf.printf "I managed to normalize this assertion\n";
						let post_heap, post_store, post_p_formulae = JSIL_Logic_Normalise.normalize_assertion_top_level post in 
						{	
							n_pre = pre_heap, pre_store, pre_p_formulae; 
							n_post = post_heap, post_store, post_p_formulae; 
							n_ret_flag = ret_flag
						}
					)
					pre_post_list in 
			let new_spec = 
				{
					n_spec_name = spec_name; 
					n_spec_params = spec_params; 
					n_proc_specs = normalized_pre_post_list
				} in 
			Hashtbl.replace spec_table spec_name new_spec 
		) 
		spec_list;  
	let spec_table_str : string = JSIL_Logic_Print.string_of_n_spec_table spec_table in 
	Printf.printf "Spec Table: \n %s" spec_table_str; 
  spec_table

let run_jsil_prog prog which_pred = 
	let heap = SHeap.create 1021 in 
	evaluate_prog prog which_pred heap; 
	let final_heap_str = SSyntax_Print.sexpr_of_heap heap in 
	Printf.printf "Final heap: \n%s\n" final_heap_str

let process_file filename =
	(* let inx = In_channel.create filename in *)
	let inx = open_in filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let prog, which_pred = parse_and_preprocess_jsil_prog lexbuf in
	close_in inx;
	(if (!jsil_run)
	   then run_jsil_prog prog which_pred
		 else ())

let process_specs filename = 
	match filename with 
	| None -> () 
	| Some filename -> 
		let inx = open_in filename in
		let lexbuf = Lexing.from_channel inx in
		lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
		let specs = parse_and_print_logic lexbuf in 
		close_in inx

let main () = 
	arguments ();
	process_file !file; 
	(* Printf.printf "Finished parsing! %s\n" !file; *)
	process_specs !specs 

let _ = main()